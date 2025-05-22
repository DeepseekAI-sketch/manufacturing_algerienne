# app.py - Logiciel de Gestion de Production Industrielle (ManufacturingSoft Algérie)
# Système intégré pour les entreprises manufacturières algériennes
# Version 2.0.0 - Mai 2025

from flask import Flask, render_template, request, redirect, url_for, flash, session, jsonify, send_file, abort, Response
import pymysql
import platform
import os
import secrets
from datetime import datetime, timedelta, date
import pandas as pd
import numpy as np
import matplotlib
matplotlib.use('Agg')  # Pour éviter les problèmes de thread
import matplotlib.pyplot as plt
from matplotlib.backends.backend_agg import FigureCanvasAgg as FigureCanvas
import seaborn as sns
import io
import base64
import json
import csv
import qrcode
import barcode
from barcode.writer import ImageWriter
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.utils import secure_filename
from functools import wraps
import logging
from logging.handlers import RotatingFileHandler, TimedRotatingFileHandler
import uuid
import re
import time
import calendar
import pdfkit
from flask_wtf import CSRFProtect
from flask_wtf.csrf import CSRFError
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
from flask_mail import Mail, Message
from itsdangerous import URLSafeTimedSerializer, SignatureExpired, BadTimeSignature
import pytz
from decimal import Decimal
import threading
import random
import string
from sqlalchemy import create_engine, text
import plotly.express as px
import plotly.graph_objects as go
import plotly.io as pio
from plotly.subplots import make_subplots
from flask_caching import Cache
import redis
import requests
from PIL import Image, ImageDraw, ImageFont
import socket
import xlsxwriter
import hashlib


# =============================================================================
# CONFIGURATION
# =============================================================================

# Configuration de l'application Flask
app = Flask(__name__)
app.config.from_object('config.ProductionConfig')  # Chargement de la configuration
app.secret_key = os.environ.get('SECRET_KEY', secrets.token_hex(32))
csrf = CSRFProtect(app)  # Protection CSRF



# Configuration du cache
cache = Cache(app, config={'CACHE_TYPE': 'simple'})

# Configuration pour les téléchargements de fichiers
UPLOAD_FOLDER = os.environ.get('UPLOAD_FOLDER', 'static/uploads')
ALLOWED_EXTENSIONS = {'pdf', 'png', 'jpg', 'jpeg', 'csv', 'xlsx', 'doc', 'docx', 'json', 'xml', 'txt'}
app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER
app.config['MAX_CONTENT_LENGTH'] = 32 * 1024 * 1024  # Limite: 32 Mo


# Configuration des logs
LOG_FOLDER = os.environ.get('LOG_FOLDER', 'logs')
os.makedirs(LOG_FOLDER, exist_ok=True)
os.makedirs(app.config['UPLOAD_FOLDER'], exist_ok=True)

# Configuration du logger principal
logger = logging.getLogger('production_app')
logger.setLevel(logging.INFO)

# Handler pour fichier journalier avec rotation
file_handler = TimedRotatingFileHandler(
    os.path.join(LOG_FOLDER, 'production_app.log'),
    when='midnight',
    interval=1,
    backupCount=30
)
file_handler.setLevel(logging.INFO)
file_handler.setFormatter(logging.Formatter(
    '%(asctime)s - %(name)s - %(levelname)s - [%(module)s:%(lineno)d] - %(message)s'
))
logger.addHandler(file_handler)

# Handler pour les erreurs uniquement
error_handler = RotatingFileHandler(
    os.path.join(LOG_FOLDER, 'errors.log'),
    maxBytes=10485760,  # 10MB
    backupCount=10
)
error_handler.setLevel(logging.ERROR)
error_handler.setFormatter(logging.Formatter(
    '%(asctime)s - %(name)s - %(levelname)s - [%(module)s:%(lineno)d] - %(message)s'
))
logger.addHandler(error_handler)

# Configuration du limiteur de débit (pour prévenir les attaques brute force)
limiter = Limiter(
    get_remote_address,
    app=app,
    default_limits=["200 per day", "50 per hour"],
    storage_uri="memory://"
)

# Configuration de l'envoi d'emails
mail = Mail(app)
serializer = URLSafeTimedSerializer(app.config['SECRET_KEY'])

# Configuration timezone
tz_algeria = pytz.timezone('Africa/Algiers')

# Configuration de la connexion à la base de données
db_config = {
    'host': os.environ.get('DB_HOST', 'localhost'),
    'user': os.environ.get('DB_USER', 'root'),
    'password': os.environ.get('DB_PASSWORD', ''),
    'database': os.environ.get('DB_NAME', 'db_manufacturing_algerienne'),
    'charset': 'utf8mb4',
    'collation': 'utf8mb4_general_ci',
    'cursorclass': pymysql.cursors.DictCursor
}

# SQLAlchemy pour analyses complexes
engine = create_engine(f"mysql+pymysql://{db_config['user']}:{db_config['password']}@{db_config['host']}/{db_config['database']}?charset=utf8mb4")

@app.context_processor
def utility_processor():
    def has_permission(required_role):
        """Vérifie si l'utilisateur a la permission requise."""
        user_role = session.get('role', None)
        
        # Si aucun rôle n'est défini, l'utilisateur n'est pas connecté
        if not user_role:
            return False
        
        # Définir la hiérarchie des rôles (du plus bas au plus élevé)
        role_hierarchy = ['viewer', 'operator', 'supervisor', 'manager', 'admin', 'superadmin']
        
        # Vérifier si le rôle de l'utilisateur est supérieur ou égal au rôle requis
        try:
            return role_hierarchy.index(user_role) >= role_hierarchy.index(required_role)
        except ValueError:
            return False
    
    return dict(has_permission=has_permission)

# Fonctions utilitaires

def get_date_algeria():
    """Récupère la date et l'heure actuelle en Algérie."""
    return datetime.now(tz_algeria)

def get_db_connection():
    """Établit et retourne une connexion à la base de données."""
    try:
        connection = pymysql.connect(**db_config)
        return connection
    except Exception as e:
        logger.error(f"Erreur de connexion à la base de données: {e}")
        return None

def allowed_file(filename):
    """Vérifie si l'extension de fichier est autorisée."""
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS

def generate_unique_filename(filename):
    """Génère un nom de fichier unique pour éviter les collisions."""
    ext = filename.rsplit('.', 1)[1].lower() if '.' in filename else ''
    unique_id = uuid.uuid4().hex
    timestamp = datetime.now().strftime('%Y%m%d%H%M%S')
    return f"{timestamp}_{unique_id}.{ext}" if ext else f"{timestamp}_{unique_id}"

def sanitize_filename(filename):
    """Nettoie le nom de fichier pour le rendre sûr."""
    # Supprimer les caractères non alphanumériques (sauf le point pour l'extension)
    filename = re.sub(r'[^\w\.\-]', '_', filename)
    # Limiter la longueur du nom de fichier
    if len(filename) > 100:
        name, ext = os.path.splitext(filename)
        filename = name[:95] + ext
    return filename

def generate_report_name(prefix, report_type, date_debut=None, date_fin=None):
    """Génère un nom de rapport standardisé."""
    timestamp = datetime.now().strftime('%Y%m%d%H%M%S')
    date_str = ""
    if date_debut and date_fin:
        date_str = f"_{date_debut}_au_{date_fin}"
    return f"{prefix}_{report_type}{date_str}_{timestamp}"

def create_qr_code(data, filename=None):
    """Crée un QR code à partir des données."""
    qr = qrcode.QRCode(
        version=1,
        error_correction=qrcode.constants.ERROR_CORRECT_L,
        box_size=10,
        border=4,
    )
    qr.add_data(data)
    qr.make(fit=True)
    
    img = qr.make_image(fill_color="black", back_color="white")
    
    if filename:
        path = os.path.join(app.config['UPLOAD_FOLDER'], 'qrcodes', filename)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        img.save(path)
        return path
    else:
        buf = io.BytesIO()
        img.save(buf)
        buf.seek(0)
        return buf

def create_barcode(data, filename=None):
    """Crée un code-barres à partir des données."""
    code128 = barcode.get_barcode_class('code128')
    code = code128(data, writer=ImageWriter())
    
    if filename:
        path = os.path.join(app.config['UPLOAD_FOLDER'], 'barcodes', filename)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        fullname = code.save(path)
        return fullname
    else:
        buf = io.BytesIO()
        code.write(buf)
        buf.seek(0)
        return buf

def send_notification_email(subject, recipients, body):
    """Envoie un email de notification."""
    try:
        msg = Message(
            subject=subject,
            recipients=recipients,
            body=body,
            sender=app.config['MAIL_DEFAULT_SENDER']
        )
        mail.send(msg)
        logger.info(f"Email de notification envoyé à {recipients}")
        return True
    except Exception as e:
        logger.error(f"Erreur d'envoi d'email: {e}")
        return False

def format_currency(amount):
    """Formate un montant en monnaie algérienne (DZD)."""
    if amount is None:
        return "0,00 DA"
    return f"{amount:,.2f} DA".replace(",", " ").replace(".", ",")

def calculate_business_days(start_date, end_date):
    """Calcule le nombre de jours ouvrables entre deux dates."""
    business_days = 0
    current_date = start_date
    while current_date <= end_date:
        # 0 = lundi, 1 = mardi, ..., 4 = vendredi, 5 = samedi (demi-journée en Algérie), 6 = dimanche
        weekday = current_date.weekday()
        # En Algérie, la semaine de travail est généralement du dimanche au jeudi
        if weekday < 5:  # Du lundi au vendredi
            business_days += 1
        elif weekday == 5:  # Samedi (demi-journée)
            business_days += 0.5
        current_date += timedelta(days=1)
    return business_days

# Fonctions de gestion des permissions
def current_user_role():
    """Récupère le rôle de l'utilisateur actuellement connecté."""
    return session.get('role', None)

def has_permission(required_role):
    """Vérifie si l'utilisateur a la permission requise."""
    user_role = current_user_role()
    
    # Si aucun rôle n'est défini, l'utilisateur n'est pas connecté
    if not user_role:
        return False
    
    # Définir la hiérarchie des rôles (du plus bas au plus élevé)
    role_hierarchy = ['viewer', 'operator', 'supervisor', 'manager', 'admin', 'superadmin']
    
    # Vérifier si le rôle de l'utilisateur est supérieur ou égal au rôle requis
    return role_hierarchy.index(user_role) >= role_hierarchy.index(required_role)

# =============================================================================
# DÉCORATEURS
# =============================================================================

def login_required(f):
    """Décorateur pour vérifier l'authentification."""
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'user_id' not in session:
            flash('Veuillez vous connecter pour accéder à cette page', 'warning')
            return redirect(url_for('login', next=request.url))
        return f(*args, **kwargs)
    return decorated_function

def role_required(role):
    """Décorateur pour vérifier le rôle de l'utilisateur."""
    def decorator(f):
        @wraps(f)
        def decorated_function(*args, **kwargs):
            if not has_permission(role):
                flash(f'Vous devez avoir le rôle {role} ou supérieur pour accéder à cette page', 'danger')
                return redirect(url_for('index'))
            return f(*args, **kwargs)
        return decorated_function
    return decorator

def log_activity(activity_type):
    """Décorateur pour journaliser les activités importantes."""
    def decorator(f):
        @wraps(f)
        def decorated_function(*args, **kwargs):
            start_time = time.time()
            result = f(*args, **kwargs)
            execution_time = time.time() - start_time
            
            if 'user_id' in session:
                try:
                    conn = get_db_connection()
                    if conn:
                        with conn.cursor() as cursor:
                            cursor.execute("""
                                INSERT INTO logs_activite 
                                (utilisateur_id, type_activite, url, methode, ip, temps_execution, date_creation)
                                VALUES (%s, %s, %s, %s, %s, %s, %s)
                            """, (
                                session['user_id'], 
                                activity_type, 
                                request.path, 
                                request.method, 
                                request.remote_addr, 
                                execution_time,
                                datetime.now()
                            ))
                            conn.commit()
                except Exception as e:
                    logger.error(f"Erreur de journalisation d'activité: {e}")
                finally:
                    if conn:
                        conn.close()
            
            return result
        return decorated_function
    return decorator

def audit_trail(entity_type):
    """Décorateur pour enregistrer les modifications d'entités."""
    def decorator(f):
        @wraps(f)
        def decorated_function(*args, **kwargs):
            # Récupérer les données avant modification si mise à jour
            entity_id = kwargs.get('id')
            entity_before = None
            
            if entity_id and request.method in ['PUT', 'PATCH', 'POST'] and 'user_id' in session:
                conn = get_db_connection()
                if conn:
                    try:
                        with conn.cursor() as cursor:
                            # Récupérer l'état avant modification
                            cursor.execute(f"SELECT * FROM {entity_type} WHERE id = %s", (entity_id,))
                            entity_before = cursor.fetchone()
                    except Exception as e:
                        logger.error(f"Erreur audit trail (avant): {e}")
                    finally:
                        conn.close()
            
            # Exécuter la fonction
            result = f(*args, **kwargs)
            
            # Enregistrer l'audit après modification
            if entity_id and request.method in ['PUT', 'PATCH', 'POST'] and 'user_id' in session:
                conn = get_db_connection()
                if conn:
                    try:
                        with conn.cursor() as cursor:
                            # Récupérer l'état après modification
                            cursor.execute(f"SELECT * FROM {entity_type} WHERE id = %s", (entity_id,))
                            entity_after = cursor.fetchone()
                            
                            if entity_before and entity_after:
                                # Calculer les différences
                                changes = {}
                                for key in entity_after:
                                    if key in entity_before and entity_before[key] != entity_after[key]:
                                        changes[key] = {
                                            'before': entity_before[key],
                                            'after': entity_after[key]
                                        }
                                
                                if changes:
                                    # Enregistrer l'audit
                                    cursor.execute("""
                                        INSERT INTO audit_trail 
                                        (entite_type, entite_id, utilisateur_id, modifications, date_creation)
                                        VALUES (%s, %s, %s, %s, %s)
                                    """, (
                                        entity_type,
                                        entity_id,
                                        session['user_id'],
                                        json.dumps(changes),
                                        datetime.now()
                                    ))
                                    conn.commit()
                    except Exception as e:
                        logger.error(f"Erreur audit trail (après): {e}")
                    finally:
                        conn.close()
            
            return result
        return decorated_function
    return decorator

# =============================================================================
# GESTIONNAIRES D'ERREURS
# =============================================================================

@app.errorhandler(CSRFError)
def handle_csrf_error(e):
    """Gestionnaire pour les erreurs CSRF."""
    logger.warning(f"Tentative CSRF détectée: {request.remote_addr}")
    return render_template('error.html', error_message="Erreur de sécurité. Veuillez réessayer.", code=400), 400

@app.errorhandler(404)
def page_not_found(e):
    """Gestionnaire pour les erreurs 404 (Page non trouvée)."""
    logger.info(f"Page non trouvée: {request.path} - IP: {request.remote_addr}")
    return render_template('error.html', error_message="Page non trouvée", code=404), 404

@app.errorhandler(403)
def forbidden(e):
    """Gestionnaire pour les erreurs 403 (Accès refusé)."""
    logger.warning(f"Tentative d'accès non autorisé: {request.path} - IP: {request.remote_addr}")
    return render_template('error.html', error_message="Accès refusé", code=403), 403

@app.errorhandler(500)
def server_error(e):
    """Gestionnaire pour les erreurs 500 (Erreur interne du serveur)."""
    logger.error(f"Erreur serveur: {str(e)} - URL: {request.path} - IP: {request.remote_addr}")
    return render_template('error.html', 
                          error_message="Erreur interne du serveur. L'administrateur a été notifié.", 
                          code=500), 500

@app.errorhandler(429)
def too_many_requests(e):
    """Gestionnaire pour les erreurs 429 (Trop de requêtes)."""
    logger.warning(f"Trop de requêtes: {request.remote_addr} - {request.path}")
    return render_template('error.html', 
                          error_message="Trop de requêtes. Veuillez réessayer plus tard.", 
                          code=429), 429

# =============================================================================
# ROUTES D'AUTHENTIFICATION ET UTILISATEURS
# =============================================================================

@app.route('/login', methods=['GET', 'POST'])
@limiter.limit("10 per minute")
def login():
    """Route de connexion utilisateur."""
    next_page = request.args.get('next')
    
    if 'user_id' in session:
        return redirect(next_page or url_for('index'))
    
    if request.method == 'POST':
        username = request.form.get('username')
        password = request.form.get('password')
        remember_me = request.form.get('remember_me') == 'on'
        
        conn = get_db_connection()
        if conn:
            try:
                with conn.cursor() as cursor:
                    sql = "SELECT * FROM utilisateurs WHERE nom_utilisateur = %s AND actif = 1"
                    cursor.execute(sql, (username,))
                    user = cursor.fetchone()
                    
                    if user and check_password_hash(user['mot_de_passe'], password):
                        # Mettre à jour la dernière connexion
                        cursor.execute("""
                            UPDATE utilisateurs 
                            SET derniere_connexion = %s
                            WHERE id = %s
                        """, (datetime.now(), user['id']))
                        conn.commit()
                        
                        session['user_id'] = user['id']
                        session['username'] = user['nom_utilisateur']
                        session['role'] = user['role']
                        session['prenom'] = user['prenom']
                        session['nom'] = user['nom']
                        session['preferences'] = json.loads(user.get('preferences', '{}') or '{}')
                        
                        if remember_me:
                            # Session permanente pour "Se souvenir de moi"
                            session.permanent = True
                            app.permanent_session_lifetime = timedelta(days=30)
                        
                        logger.info(f"Connexion réussie: {username} (ID: {user['id']}) depuis {request.remote_addr}")
                        flash(f'Bienvenue, {user["prenom"]}!', 'success')
                        
                        # Enregistrer la connexion dans les logs
                        cursor.execute("""
                            INSERT INTO logs_connexion 
                            (utilisateur_id, action, ip, user_agent, date_creation)
                            VALUES (%s, %s, %s, %s, %s)
                        """, (
                            user['id'], 
                            'connexion', 
                            request.remote_addr, 
                            request.user_agent.string,
                            datetime.now()
                        ))
                        conn.commit()
                        
                        return redirect(next_page or url_for('index'))
                    else:
                        flash('Identifiants incorrects ou compte désactivé', 'danger')
                        logger.warning(f"Tentative de connexion échouée: {username} depuis {request.remote_addr}")
                        
                        # Si l'utilisateur existe mais mot de passe incorrect, incrémenter le compteur
                        if user:
                            cursor.execute("""
                                UPDATE utilisateurs 
                                SET tentatives_echec = tentatives_echec + 1
                                WHERE id = %s
                            """, (user['id'],))
                            
                            # Verrouiller le compte après 5 tentatives
                            if user['tentatives_echec'] >= 4:  # Sera 5 après l'incrémentation
                                cursor.execute("""
                                    UPDATE utilisateurs 
                                    SET actif = 0, date_verrouillage = %s
                                    WHERE id = %s
                                """, (datetime.now(), user['id']))
                                flash('Compte verrouillé après trop de tentatives. Contactez l\'administrateur.', 'danger')
                                logger.warning(f"Compte verrouillé: {username} après {user['tentatives_echec'] + 1} tentatives")
                            
                            conn.commit()
                        
                        # Enregistrer la tentative échouée dans les logs
                        cursor.execute("""
                            INSERT INTO logs_connexion 
                            (utilisateur_id, action, ip, user_agent, date_creation)
                            VALUES (%s, %s, %s, %s, %s)
                        """, (
                            user['id'] if user else None, 
                            'echec_connexion', 
                            request.remote_addr, 
                            request.user_agent.string,
                            datetime.now()
                        ))
                        conn.commit()
            except Exception as e:
                flash(f'Erreur lors de la connexion: {str(e)}', 'danger')
                logger.error(f"Erreur lors de la connexion: {str(e)}")
            finally:
                conn.close()
        else:
            flash('Impossible de se connecter à la base de données', 'danger')
    
    return render_template('login.html')

@app.route('/logout')
def logout():
    """Route de déconnexion utilisateur."""
    user_id = session.get('user_id')
    username = session.get('username', 'Utilisateur inconnu')
    
    # Enregistrer la déconnexion dans les logs
    if user_id:
        conn = get_db_connection()
        if conn:
            try:
                with conn.cursor() as cursor:
                    cursor.execute("""
                        INSERT INTO logs_connexion 
                        (utilisateur_id, action, ip, user_agent, date_creation)
                        VALUES (%s, %s, %s, %s, %s)
                    """, (
                        user_id, 
                        'deconnexion', 
                        request.remote_addr, 
                        request.user_agent.string,
                        datetime.now()
                    ))
                    conn.commit()
            except Exception as e:
                logger.error(f"Erreur lors de l'enregistrement de la déconnexion: {str(e)}")
            finally:
                conn.close()
    
    session.clear()
    logger.info(f"Déconnexion: {username} depuis {request.remote_addr}")
    flash('Vous êtes déconnecté', 'info')
    return redirect(url_for('login'))

@app.route('/mot-de-passe-oublie', methods=['GET', 'POST'])
@limiter.limit("5 per hour")
def mot_de_passe_oublie():
    """Route pour la réinitialisation du mot de passe."""
    if request.method == 'POST':
        email = request.form.get('email')
        
        conn = get_db_connection()
        if conn:
            try:
                with conn.cursor() as cursor:
                    # Vérifier si l'email existe
                    cursor.execute("SELECT id, nom, prenom FROM utilisateurs WHERE email = %s AND actif = 1", (email,))
                    user = cursor.fetchone()
                    
                    if user:
                        # Générer un token unique valide pour 24 heures
                        token = serializer.dumps(email, salt='password-reset-salt')
                        
                        # Enregistrer le token dans la base de données
                        expiration = datetime.now() + timedelta(hours=24)
                        cursor.execute("""
                            INSERT INTO tokens_reinitialisation 
                            (utilisateur_id, token, date_expiration, date_creation)
                            VALUES (%s, %s, %s, %s)
                        """, (user['id'], token, expiration, datetime.now()))
                        conn.commit()
                        
                        # Envoyer l'email avec le lien de réinitialisation
                        reset_url = url_for('reinitialiser_mot_de_passe', token=token, _external=True)
                        
                        msg = Message(
                            subject='Réinitialisation de votre mot de passe - ManufacturingSoft Algérie',
                            recipients=[email],
                            body=f"""
Bonjour {user['prenom']} {user['nom']},

Vous avez demandé la réinitialisation de votre mot de passe pour votre compte ManufacturingSoft Algérie.

Pour réinitialiser votre mot de passe, veuillez cliquer sur le lien suivant:
{reset_url}

Ce lien est valable pour 24 heures.

Si vous n'avez pas demandé cette réinitialisation, veuillez ignorer cet email.

Cordialement,
L'équipe ManufacturingSoft Algérie
                            """,
                            sender=app.config['MAIL_DEFAULT_SENDER']
                        )
                        mail.send(msg)
                        
                        logger.info(f"Demande de réinitialisation de mot de passe envoyée pour {email}")
                    
                    # Toujours afficher le même message pour éviter les fuites d'information
                    flash('Si votre email est dans notre base de données, vous recevrez un lien de réinitialisation.', 'info')
                    return redirect(url_for('login'))
            except Exception as e:
                flash('Une erreur s\'est produite. Veuillez réessayer plus tard.', 'danger')
                logger.error(f"Erreur lors de la demande de réinitialisation: {str(e)}")
            finally:
                conn.close()
    
    return render_template('mot_de_passe_oublie.html')



@app.route('/reinitialiser-mot-de-passe/<token>', methods=['GET', 'POST'])
def reinitialiser_mot_de_passe(token):
    """Route pour réinitialiser le mot de passe avec un token."""
    # Vérifier si le token est valide
    try:
        conn = get_db_connection()
        if conn:
            try:
                with conn.cursor() as cursor:
                    # Vérifier si le token existe et n'est pas expiré
                    cursor.execute("""
                        SELECT t.*, u.email 
                        FROM tokens_reinitialisation t
                        JOIN utilisateurs u ON t.utilisateur_id = u.id
                        WHERE t.token = %s AND t.utilise = 0 AND t.date_expiration > %s
                    """, (token, datetime.now()))
                    token_info = cursor.fetchone()
                    
                    if not token_info:
                        flash('Lien de réinitialisation invalide ou expiré.', 'danger')
                        return redirect(url_for('login'))
                    
                    # Vérifier le token avec itsdangerous
                    email = serializer.loads(token, salt='password-reset-salt', max_age=86400)  # 24 heures
                    
                    if email != token_info['email']:
                        flash('Lien de réinitialisation invalide.', 'danger')
                        return redirect(url_for('login'))
                    
                    if request.method == 'POST':
                        password = request.form.get('password')
                        confirm_password = request.form.get('confirm_password')
                        
                        if password != confirm_password:
                            flash('Les mots de passe ne correspondent pas.', 'danger')
                        else:
                            # Mettre à jour le mot de passe
                            hashed_password = generate_password_hash(password)
                            cursor.execute("""
                                UPDATE utilisateurs 
                                SET mot_de_passe = %s, date_modification = %s, tentatives_echec = 0, actif = 1
                                WHERE id = %s
                            """, (hashed_password, datetime.now(), token_info['utilisateur_id']))
                            
                            # Marquer le token comme utilisé
                            cursor.execute("""
                                UPDATE tokens_reinitialisation 
                                SET utilise = 1, date_utilisation = %s
                                WHERE id = %s
                            """, (datetime.now(), token_info['id']))
                            
                            conn.commit()
                            
                            flash('Votre mot de passe a été réinitialisé avec succès. Vous pouvez maintenant vous connecter.', 'success')
                            logger.info(f"Mot de passe réinitialisé pour utilisateur ID {token_info['utilisateur_id']}")
                            return redirect(url_for('login'))
            except (SignatureExpired, BadTimeSignature) as e:
                flash('Lien de réinitialisation invalide ou expiré.', 'danger')
                logger.warning(f"Tentative d'utilisation d'un token invalide/expiré: {e}")
                return redirect(url_for('login'))
            except Exception as e:
                flash('Une erreur s\'est produite. Veuillez réessayer plus tard.', 'danger')
                logger.error(f"Erreur lors de la réinitialisation du mot de passe: {str(e)}")
            finally:
                conn.close()
    except Exception as e:
        flash('Une erreur s\'est produite. Veuillez réessayer plus tard.', 'danger')
        logger.error(f"Erreur lors de la vérification du token: {str(e)}")
        return redirect(url_for('login'))
    
    return render_template('reinitialiser_mot_de_passe.html', token=token)

@app.route('/mon-profil', methods=['GET', 'POST'])
@login_required
def mon_profil():
    """Route pour consulter et modifier son profil."""
    conn = get_db_connection()
    user = None
    historique_connexions = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer les informations de l'utilisateur
                cursor.execute("""
                    SELECT id, nom, prenom, nom_utilisateur, email, role, 
                           date_creation, derniere_connexion, preferences
                    FROM utilisateurs 
                    WHERE id = %s
                """, (session['user_id'],))
                user = cursor.fetchone()
                
                if not user:
                    flash('Utilisateur introuvable', 'danger')
                    return redirect(url_for('index'))
                
                # Historique des dernières connexions
                cursor.execute("""
                    SELECT action, ip, user_agent, date_creation
                    FROM logs_connexion
                    WHERE utilisateur_id = %s
                    ORDER BY date_creation DESC
                    LIMIT 10
                """, (session['user_id'],))
                historique_connexions = cursor.fetchall()
                
                # Traitement du formulaire de modification du profil
                if request.method == 'POST':
                    action = request.form.get('action')
                    
                    if action == 'update_info':
                        # Mise à jour des informations personnelles
                        email = request.form.get('email')
                        preferences_theme = request.form.get('preferences_theme', 'light')
                        preferences_langue = request.form.get('preferences_langue', 'fr')
                        
                        # Vérifier si l'email existe déjà pour un autre utilisateur
                        cursor.execute("""
                            SELECT id FROM utilisateurs 
                            WHERE email = %s AND id != %s
                        """, (email, session['user_id']))
                        existing_email = cursor.fetchone()
                        
                        if existing_email:
                            flash('Cet email est déjà utilisé par un autre compte', 'danger')
                        else:
                            # Mettre à jour les préférences
                            preferences = {
                                'theme': preferences_theme,
                                'langue': preferences_langue
                            }
                            
                            # Mettre à jour l'utilisateur
                            cursor.execute("""
                                UPDATE utilisateurs 
                                SET email = %s, preferences = %s, date_modification = %s
                                WHERE id = %s
                            """, (email, json.dumps(preferences), datetime.now(), session['user_id']))
                            conn.commit()
                            
                            # Mettre à jour la session
                            session['preferences'] = preferences
                            
                            flash('Profil mis à jour avec succès', 'success')
                            logger.info(f"Profil mis à jour pour utilisateur ID {session['user_id']}")
                            return redirect(url_for('mon_profil'))
                    
                    elif action == 'change_password':
                        # Changement de mot de passe
                        current_password = request.form.get('current_password')
                        new_password = request.form.get('new_password')
                        confirm_password = request.form.get('confirm_password')
                        
                        # Vérifier le mot de passe actuel
                        cursor.execute("SELECT mot_de_passe FROM utilisateurs WHERE id = %s", (session['user_id'],))
                        user_pwd = cursor.fetchone()
                        
                        if not user_pwd or not check_password_hash(user_pwd['mot_de_passe'], current_password):
                            flash('Le mot de passe actuel est incorrect', 'danger')
                        elif new_password != confirm_password:
                            flash('Les nouveaux mots de passe ne correspondent pas', 'danger')
                        else:
                            # Mettre à jour le mot de passe
                            hashed_password = generate_password_hash(new_password)
                            cursor.execute("""
                                UPDATE utilisateurs 
                                SET mot_de_passe = %s, date_modification = %s
                                WHERE id = %s
                            """, (hashed_password, datetime.now(), session['user_id']))
                            conn.commit()
                            
                            flash('Mot de passe modifié avec succès', 'success')
                            logger.info(f"Mot de passe modifié pour utilisateur ID {session['user_id']}")
                            return redirect(url_for('mon_profil'))
        except Exception as e:
            flash(f'Erreur lors de l\'accès au profil: {str(e)}', 'danger')
            logger.error(f"Erreur accès profil: {str(e)}")
        finally:
            conn.close()
    
    if user and 'preferences' in user:
        try:
            user['preferences_dict'] = json.loads(user['preferences']) if user['preferences'] else {}
        except:
            user['preferences_dict'] = {}
    
    return render_template('utilisateurs/mon_profil.html', 
                          user=user, 
                          historique_connexions=historique_connexions)




# =============================================================================
# ROUTE PRINCIPALE - TABLEAU DE BORD
# =============================================================================

@app.route('/')
@login_required
@log_activity('visite_dashboard')
def index():
    """Page d'accueil du tableau de bord."""
    stats = {}
    graphs = {}
    alertes = []
    taches_recentes = []
    
    conn = get_db_connection()
    if conn:
        try:
            with conn.cursor() as cursor:
                # Statistiques générales
                cursor.execute("SELECT COUNT(*) as total FROM produits WHERE actif = 1")
                stats['total_produits'] = cursor.fetchone()['total']
                
                cursor.execute("SELECT COUNT(*) as total FROM commandes WHERE statut = 'en_cours'")
                stats['commandes_en_cours'] = cursor.fetchone()['total']
                
                cursor.execute("SELECT COUNT(*) as total FROM maintenance WHERE statut = 'planifie'")
                stats['maintenance_planifiee'] = cursor.fetchone()['total']
                
                cursor.execute("""
                    SELECT COUNT(*) as total FROM stocks 
                    WHERE quantite < seuil_alerte AND actif = 1
                """)
                stats['produits_sous_seuil'] = cursor.fetchone()['total']
                
                # Production mensuelle (6 derniers mois)
                cursor.execute("""
                    SELECT DATE_FORMAT(date_creation, '%Y-%m') as mois, 
                    SUM(quantite_produite) as production 
                    FROM production 
                    WHERE date_creation >= DATE_SUB(NOW(), INTERVAL 6 MONTH)
                    GROUP BY mois 
                    ORDER BY mois
                """)
                production_data = cursor.fetchall()
                
                # Répartition des produits par catégorie
                cursor.execute("""
                    SELECT categorie, COUNT(*) as count 
                    FROM produits 
                    WHERE actif = 1
                    GROUP BY categorie
                """)
                categories_data = cursor.fetchall()
                
                # Alertes de stock
                cursor.execute("""
                    SELECT s.*, p.nom as produit_nom, p.reference, e.nom as entrepot_nom
                    FROM stocks s
                    JOIN produits p ON s.produit_id = p.id
                    JOIN entrepots e ON s.entrepot_id = e.id
                    WHERE s.quantite < s.seuil_alerte AND s.actif = 1
                    ORDER BY s.quantite / s.seuil_alerte ASC
                    LIMIT 5
                """)
                alertes_stock = cursor.fetchall()
                for alerte in alertes_stock:
                    alertes.append({
                        'type': 'stock',
                        'titre': f"Stock bas: {alerte['produit_nom']}",
                        'message': f"Quantité: {alerte['quantite']} / Seuil: {alerte['seuil_alerte']} à {alerte['entrepot_nom']}",
                        'lien': url_for('stocks_liste'),
                        'date': alerte['date_modification'],
                        'priorite': 'haute' if alerte['quantite'] == 0 else 'moyenne'
                    })
                
                # Maintenances à venir
                cursor.execute("""
                    SELECT m.*, e.nom as equipement_nom, t.nom as type_nom
                    FROM maintenance m
                    JOIN equipements e ON m.equipement_id = e.id
                    JOIN types_maintenance t ON m.type_maintenance_id = t.id
                    WHERE m.statut = 'planifie' AND m.date_programmee <= DATE_ADD(CURDATE(), INTERVAL 7 DAY)
                    ORDER BY m.date_programmee ASC
                    LIMIT 5
                """)
                maintenances = cursor.fetchall()
                for maintenance in maintenances:
                    jours_restants = (maintenance['date_programmee'].date() - date.today()).days
                    alertes.append({
                        'type': 'maintenance',
                        'titre': f"Maintenance: {maintenance['equipement_nom']}",
                        'message': f"{maintenance['type_nom']} prévu le {maintenance['date_programmee'].strftime('%d/%m/%Y')}",
                        'lien': url_for('maintenance_details', maintenance_id=maintenance['id']),
                        'date': maintenance['date_programmee'],
                        'priorite': 'haute' if jours_restants <= 1 else 'moyenne' if jours_restants <= 3 else 'basse'
                    })
                
                # Tâches récentes
                cursor.execute("""
                    SELECT 'production' as type, id, date_creation, 
                           CONCAT('Production de ', quantite_produite, ' unités') as description
                    FROM production
                    WHERE utilisateur_id = %s
                    UNION
                    SELECT 'qualite' as type, id, date_controle as date_creation, 
                           CONCAT('Contrôle qualité: ', resultat) as description
                    FROM controles_qualite
                    WHERE utilisateur_id = %s
                    UNION
                    SELECT 'maintenance' as type, id, date_creation, 
                           CONCAT('Maintenance: ', statut) as description
                    FROM maintenance
                    WHERE utilisateur_id = %s
                    ORDER BY date_creation DESC
                    LIMIT 10
                """, (session['user_id'], session['user_id'], session['user_id']))
                taches_recentes = cursor.fetchall()
                
            # Création des graphiques
            if production_data:
                plt.figure(figsize=(10, 4))
                plt.bar(
                    [item['mois'] for item in production_data],
                    [item['production'] for item in production_data]
                )
                plt.title('Production mensuelle')
                plt.xlabel('Mois')
                plt.ylabel('Quantité produite')
                plt.xticks(rotation=45)
                plt.tight_layout()
                
                buffer = io.BytesIO()
                plt.savefig(buffer, format='png')
                buffer.seek(0)
                graphs['production_mensuelle'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                plt.close()
            
            if categories_data:
                plt.figure(figsize=(8, 8))
                plt.pie(
                    [item['count'] for item in categories_data],
                    labels=[item['categorie'] for item in categories_data],
                    autopct='%1.1f%%'
                )
                plt.title('Répartition des produits par catégorie')
                plt.tight_layout()
                
                buffer = io.BytesIO()
                plt.savefig(buffer, format='png')
                buffer.seek(0)
                graphs['categories_produits'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                plt.close()
                
            # Graphique de qualité
            cursor.execute("""
                SELECT DATE_FORMAT(date_controle, '%Y-%m') as mois, 
                       COUNT(*) as total,
                       SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) as conformes
                FROM controles_qualite
                WHERE date_controle >= DATE_SUB(NOW(), INTERVAL 6 MONTH)
                GROUP BY mois
                ORDER BY mois
            """)
            qualite_data = cursor.fetchall()
            
            if qualite_data:
                plt.figure(figsize=(10, 4))
                mois = [item['mois'] for item in qualite_data]
                taux = [item['conformes'] / item['total'] * 100 if item['total'] > 0 else 0 for item in qualite_data]
                
                plt.plot(mois, taux, marker='o', linestyle='-')
                plt.title('Taux de conformité qualité')
                plt.xlabel('Mois')
                plt.ylabel('Taux de conformité (%)')
                plt.axhline(y=95, color='r', linestyle='--', label='Objectif 95%')
                plt.legend()
                plt.xticks(rotation=45)
                plt.tight_layout()
                
                buffer = io.BytesIO()
                plt.savefig(buffer, format='png')
                buffer.seek(0)
                graphs['qualite_mensuelle'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                plt.close()
                
        except Exception as e:
            flash(f'Erreur lors du chargement des données: {str(e)}', 'danger')
            logger.error(f"Erreur chargement dashboard: {str(e)}")
        finally:
            conn.close()
    
    return render_template('index.html', 
                          stats=stats, 
                          graphs=graphs, 
                          alertes=alertes,
                          taches_recentes=taches_recentes)

# =============================================================================
# GESTION DES PRODUITS
# =============================================================================

@app.route('/produits')
@login_required
@log_activity('liste_produits')
def produits_liste():
    """Liste des produits."""
    conn = get_db_connection()
    produits = []
    
    # Paramètres de filtrage et pagination
    page = request.args.get('page', 1, type=int)
    per_page = request.args.get('per_page', 20, type=int)
    categorie = request.args.get('categorie')
    recherche = request.args.get('recherche')
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Construire la requête de base
                sql = """
                SELECT p.*, SUM(s.quantite) as stock_total 
                FROM produits p 
                LEFT JOIN stocks s ON p.id = s.produit_id 
                WHERE p.actif = 1
                """
                params = []
                
                # Ajouter les conditions de filtrage
                if categorie:
                    sql += " AND p.categorie = %s"
                    params.append(categorie)
                
                if recherche:
                    sql += " AND (p.nom LIKE %s OR p.reference LIKE %s OR p.description LIKE %s)"
                    params.extend([f'%{recherche}%', f'%{recherche}%', f'%{recherche}%'])
                
                # Terminer la requête
                sql += " GROUP BY p.id"
                
                # Récupérer le nombre total d'enregistrements pour la pagination
                count_sql = f"SELECT COUNT(*) as total FROM ({sql}) as subquery"
                cursor.execute(count_sql, params)
                total_count = cursor.fetchone()['total']
                
                # Ajouter la pagination
                sql += " LIMIT %s OFFSET %s"
                params.extend([per_page, (page - 1) * per_page])
                
                # Exécuter la requête finale
                cursor.execute(sql, params)
                produits = cursor.fetchall()
                
                # Récupérer les catégories pour le filtre
                cursor.execute("SELECT DISTINCT categorie FROM produits WHERE actif = 1 ORDER BY categorie")
                categories = cursor.fetchall()
                
                # Calculer la pagination
                total_pages = (total_count + per_page - 1) // per_page
                pagination = {
                    'page': page,
                    'per_page': per_page,
                    'total_count': total_count,
                    'total_pages': total_pages
                }
                
        except Exception as e:
            flash(f'Erreur lors de la récupération des produits: {str(e)}', 'danger')
            logger.error(f"Erreur liste produits: {str(e)}")
        finally:
            conn.close()
    
    return render_template('produits/liste.html', 
                          produits=produits, 
                          categories=categories if 'categories' in locals() else [],
                          pagination=pagination if 'pagination' in locals() else {},
                          filtres={'categorie': categorie, 'recherche': recherche})

@app.route('/produits/ajouter', methods=['GET', 'POST'])
@login_required
@role_required('supervisor')
@log_activity('ajout_produit')
def produit_ajouter():
    """Ajout d'un nouveau produit."""
    if request.method == 'POST':
        # Récupération des données du formulaire
        nom = request.form.get('nom')
        reference = request.form.get('reference')
        description = request.form.get('description')
        categorie = request.form.get('categorie')
        prix_unitaire = request.form.get('prix_unitaire')
        tva = request.form.get('tva', 19)  # TVA par défaut en Algérie: 19%
        unite_mesure = request.form.get('unite_mesure', 'unité')
        poids = request.form.get('poids')
        dimensions = request.form.get('dimensions')
        
        conn = get_db_connection()
        if conn:
            try:
                with conn.cursor() as cursor:
                    # Vérifier si la référence existe déjà
                    cursor.execute("SELECT id FROM produits WHERE reference = %s AND actif = 1", (reference,))
                    if cursor.fetchone():
                        flash('Cette référence existe déjà', 'danger')
                        return render_template('produits/ajouter.html')
                    
                    # Téléchargement de l'image si présente
                    image_url = None
                    if 'image' in request.files:
                        image_file = request.files['image']
                        if image_file and image_file.filename != '' and allowed_file(image_file.filename):
                            secure_name = sanitize_filename(image_file.filename)
                            unique_filename = generate_unique_filename(secure_name)
                            
                            # Créer le répertoire d'images s'il n'existe pas
                            image_dir = os.path.join(app.config['UPLOAD_FOLDER'], 'produits')
                            os.makedirs(image_dir, exist_ok=True)
                            
                            filepath = os.path.join(image_dir, unique_filename)
                            image_file.save(filepath)
                            image_url = f"/static/uploads/produits/{unique_filename}"
                    
                    # Insertion du produit
                    sql = """
                    INSERT INTO produits (
                        nom, reference, description, categorie, prix_unitaire, 
                        tva, unite_mesure, poids, dimensions, image_url,
                        utilisateur_id, date_creation
                    ) VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                    """
                    cursor.execute(sql, (
                        nom, reference, description, categorie, prix_unitaire,
                        tva, unite_mesure, poids, dimensions, image_url,
                        session['user_id'], datetime.now()
                    ))
                    conn.commit()
                    
                    # Récupérer l'ID du nouveau produit
                    produit_id = cursor.lastrowid
                    
                    # Initialiser le stock à zéro dans tous les entrepôts
                    cursor.execute("SELECT id FROM entrepots WHERE actif = 1")
                    entrepots = cursor.fetchall()
                    
                    for entrepot in entrepots:
                        sql = """
                        INSERT INTO stocks (
                            produit_id, entrepot_id, quantite, seuil_alerte, 
                            utilisateur_id, date_creation
                        ) VALUES (%s, %s, %s, %s, %s, %s)
                        """
                        cursor.execute(sql, (
                            produit_id, entrepot['id'], 0, 10,  # Stock initial 0, seuil alerte 10
                            session['user_id'], datetime.now()
                        ))
                    
                    conn.commit()
                    
                    # Génération du QR code pour le produit
                    qr_data = json.dumps({
                        'id': produit_id,
                        'reference': reference,
                        'nom': nom
                    })
                    qr_filename = f"produit_{produit_id}.png"
                    create_qr_code(qr_data, qr_filename)
                    
                    # Génération du code-barres
                    barcode_data = reference
                    barcode_filename = f"produit_{produit_id}_barcode"
                    create_barcode(barcode_data, barcode_filename)
                    
                    flash('Produit ajouté avec succès', 'success')
                    logger.info(f"Produit ajouté: {nom} (ID: {produit_id}) par utilisateur ID {session['user_id']}")
                    return redirect(url_for('produits_liste'))
            except Exception as e:
                flash(f'Erreur lors de l\'ajout du produit: {str(e)}', 'danger')
                logger.error(f"Erreur ajout produit: {str(e)}")
            finally:
                conn.close()
    
    return render_template('produits/ajouter.html')

@app.route('/produits/<int:produit_id>')
@login_required
@log_activity('details_produit')
def produit_details(produit_id):
    """Détails d'un produit spécifique."""
    conn = get_db_connection()
    produit = None
    historique_stock = []
    historique_production = []
    historique_qualite = []
    stocks = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Détails du produit
                sql = """
                SELECT p.*, u.prenom, u.nom as nom_utilisateur
                FROM produits p
                LEFT JOIN utilisateurs u ON p.utilisateur_id = u.id
                WHERE p.id = %s AND p.actif = 1
                """
                cursor.execute(sql, (produit_id,))
                produit = cursor.fetchone()
                
                if not produit:
                    flash('Produit non trouvé ou désactivé', 'warning')
                    return redirect(url_for('produits_liste'))
                
                # Stocks actuels
                sql = """
                SELECT s.*, e.nom as entrepot_nom
                FROM stocks s
                JOIN entrepots e ON s.entrepot_id = e.id
                WHERE s.produit_id = %s AND s.actif = 1
                ORDER BY e.nom
                """
                cursor.execute(sql, (produit_id,))
                stocks = cursor.fetchall()
                
                # Historique des stocks
                sql = """
                SELECT m.*, e.nom as entrepot_nom, u.prenom, u.nom as nom_utilisateur 
                FROM mouvements_stock m
                JOIN entrepots e ON m.entrepot_id = e.id
                JOIN utilisateurs u ON m.utilisateur_id = u.id
                WHERE m.produit_id = %s
                ORDER BY m.date_mouvement DESC
                LIMIT 50
                """
                cursor.execute(sql, (produit_id,))
                historique_stock = cursor.fetchall()
                
                # Historique des productions
                sql = """
                SELECT p.*, l.nom as ligne_nom, u.prenom, u.nom as nom_utilisateur
                FROM production p
                JOIN lignes_production l ON p.ligne_production_id = l.id
                JOIN utilisateurs u ON p.utilisateur_id = u.id
                WHERE p.produit_id = %s
                ORDER BY p.date_creation DESC
                LIMIT 50
                """
                cursor.execute(sql, (produit_id,))
                historique_production = cursor.fetchall()
                
                # Historique des contrôles qualité
                sql = """
                SELECT c.*, u.prenom, u.nom as nom_utilisateur
                FROM controles_qualite c
                JOIN utilisateurs u ON c.utilisateur_id = u.id
                WHERE c.produit_id = %s
                ORDER BY c.date_controle DESC
                LIMIT 50
                """
                cursor.execute(sql, (produit_id,))
                historique_qualite = cursor.fetchall()
                
                # Statistiques de production
                cursor.execute("""
                    SELECT AVG(temps_production) as temps_moyen,
                           AVG(quantite_produite) as quantite_moyenne,
                           SUM(quantite_produite) as quantite_totale,
                           MAX(date_creation) as derniere_production
                    FROM production
                    WHERE produit_id = %s
                """, (produit_id,))
                stats_production = cursor.fetchone()
                
                # Statistiques de qualité
                cursor.execute("""
                    SELECT COUNT(*) as total,
                           SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) as conformes,
                           SUM(CASE WHEN resultat = 'non_conforme' THEN 1 ELSE 0 END) as non_conformes
                    FROM controles_qualite
                    WHERE produit_id = %s
                """, (produit_id,))
                stats_qualite = cursor.fetchone()
                
                if stats_qualite and stats_qualite['total'] > 0:
                    stats_qualite['taux_conformite'] = (stats_qualite['conformes'] / stats_qualite['total']) * 100
                else:
                    stats_qualite = {'total': 0, 'conformes': 0, 'non_conformes': 0, 'taux_conformite': 0}
                
                # Préparer les données pour le graphique d'historique des stocks
                cursor.execute("""
                    SELECT DATE_FORMAT(date_mouvement, '%Y-%m-%d') as date, 
                           SUM(CASE WHEN type_mouvement IN ('entree', 'production', 'inventaire_plus') 
                                THEN quantite ELSE 0 END) as entrees,
                           SUM(CASE WHEN type_mouvement IN ('sortie', 'inventaire_moins') 
                                THEN quantite ELSE 0 END) as sorties
                    FROM mouvements_stock
                    WHERE produit_id = %s
                    GROUP BY DATE_FORMAT(date_mouvement, '%Y-%m-%d')
                    ORDER BY date
                    LIMIT 30
                """, (produit_id,))
                donnees_graphique = cursor.fetchall()
                
                if donnees_graphique:
                    plt.figure(figsize=(10, 4))
                    
                    dates = [item['date'] for item in donnees_graphique]
                    entrees = [item['entrees'] for item in donnees_graphique]
                    sorties = [item['sorties'] for item in donnees_graphique]
                    
                    plt.bar(dates, entrees, label='Entrées', color='green', alpha=0.7)
                    plt.bar(dates, sorties, label='Sorties', color='red', alpha=0.7)
                    
                    plt.title('Mouvements de stock')
                    plt.xlabel('Date')
                    plt.ylabel('Quantité')
                    plt.legend()
                    plt.xticks(rotation=45)
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    graphique_stock = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                else:
                    graphique_stock = None
                
        except Exception as e:
            flash(f'Erreur lors de la récupération des détails du produit: {str(e)}', 'danger')
            logger.error(f"Erreur détails produit {produit_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('produits/details.html', 
                          produit=produit, 
                          stocks=stocks,
                          historique_stock=historique_stock,
                          historique_production=historique_production,
                          historique_qualite=historique_qualite,
                          stats_production=stats_production if 'stats_production' in locals() else None,
                          stats_qualite=stats_qualite if 'stats_qualite' in locals() else None,
                          graphique_stock=graphique_stock if 'graphique_stock' in locals() else None)

@app.route('/produits/modifier/<int:produit_id>', methods=['GET', 'POST'])
@login_required
@role_required('supervisor')
@log_activity('modification_produit')
@audit_trail('produits')
def produit_modifier(produit_id):
    """Modification d'un produit existant."""
    conn = get_db_connection()
    produit = None
    
    if conn:
        try:
            with conn.cursor() as cursor:
                sql = "SELECT * FROM produits WHERE id = %s AND actif = 1"
                cursor.execute(sql, (produit_id,))
                produit = cursor.fetchone()
                
                if not produit:
                    flash('Produit non trouvé ou désactivé', 'warning')
                    return redirect(url_for('produits_liste'))
                
                if request.method == 'POST':
                    nom = request.form.get('nom')
                    reference = request.form.get('reference')
                    description = request.form.get('description')
                    categorie = request.form.get('categorie')
                    prix_unitaire = request.form.get('prix_unitaire')
                    tva = request.form.get('tva')
                    unite_mesure = request.form.get('unite_mesure')
                    poids = request.form.get('poids')
                    dimensions = request.form.get('dimensions')
                    
                    # Vérifier si la référence existe déjà pour un autre produit
                    cursor.execute("""
                        SELECT id FROM produits 
                        WHERE reference = %s AND id != %s AND actif = 1
                    """, (reference, produit_id))
                    if cursor.fetchone():
                        flash('Cette référence existe déjà pour un autre produit', 'danger')
                    else:
                        # Gestion de l'image
                        image_url = produit['image_url']
                        if 'image' in request.files:
                            image_file = request.files['image']
                            if image_file and image_file.filename != '' and allowed_file(image_file.filename):
                                # Supprimer l'ancienne image si elle existe
                                if image_url:
                                    old_path = os.path.join(app.root_path, image_url.lstrip('/'))
                                    if os.path.exists(old_path):
                                        os.remove(old_path)
                                
                                # Enregistrer la nouvelle image
                                secure_name = sanitize_filename(image_file.filename)
                                unique_filename = generate_unique_filename(secure_name)
                                
                                image_dir = os.path.join(app.config['UPLOAD_FOLDER'], 'produits')
                                os.makedirs(image_dir, exist_ok=True)
                                
                                filepath = os.path.join(image_dir, unique_filename)
                                image_file.save(filepath)
                                image_url = f"/static/uploads/produits/{unique_filename}"
                        
                        # Mise à jour du produit
                        sql = """
                        UPDATE produits 
                        SET nom = %s, reference = %s, description = %s, categorie = %s, 
                            prix_unitaire = %s, tva = %s, unite_mesure = %s, poids = %s, 
                            dimensions = %s, image_url = %s, date_modification = %s
                        WHERE id = %s
                        """
                        cursor.execute(sql, (
                            nom, reference, description, categorie, 
                            prix_unitaire, tva, unite_mesure, poids,
                            dimensions, image_url, datetime.now(), produit_id
                        ))
                        conn.commit()
                        
                        # Mise à jour du code-barres si la référence a changé
                        if reference != produit['reference']:
                            barcode_filename = f"produit_{produit_id}_barcode"
                            create_barcode(reference, barcode_filename)
                        
                        flash('Produit modifié avec succès', 'success')
                        logger.info(f"Produit modifié: ID {produit_id} par utilisateur ID {session['user_id']}")
                        return redirect(url_for('produit_details', produit_id=produit_id))
        except Exception as e:
            flash(f'Erreur lors de la modification du produit: {str(e)}', 'danger')
            logger.error(f"Erreur modification produit {produit_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('produits/modifier.html', produit=produit)

@app.route('/produits/supprimer/<int:produit_id>', methods=['POST'])
@login_required
@role_required('manager')
@log_activity('suppression_produit')
def produit_supprimer(produit_id):
    """Désactivation d'un produit (suppression logique)."""
    conn = get_db_connection()
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Vérifier si le produit existe
                cursor.execute("SELECT id FROM produits WHERE id = %s AND actif = 1", (produit_id,))
                if not cursor.fetchone():
                    flash('Produit non trouvé ou déjà désactivé', 'warning')
                    return redirect(url_for('produits_liste'))
                
                # Vérifier s'il y a des dépendances actives
                cursor.execute("""
                    SELECT COUNT(*) as total FROM production 
                    WHERE produit_id = %s AND date_creation > DATE_SUB(NOW(), INTERVAL 30 DAY)
                """, (produit_id,))
                if cursor.fetchone()['total'] > 0:
                    flash('Ce produit a été utilisé récemment dans la production et ne peut pas être supprimé', 'danger')
                    return redirect(url_for('produit_details', produit_id=produit_id))
                
                # Désactiver le produit (suppression logique)
                cursor.execute("""
                    UPDATE produits 
                    SET actif = 0, date_suppression = %s
                    WHERE id = %s
                """, (datetime.now(), produit_id))
                
                # Désactiver également les stocks associés
                cursor.execute("""
                    UPDATE stocks 
                    SET actif = 0, date_suppression = %s
                    WHERE produit_id = %s
                """, (datetime.now(), produit_id))
                
                conn.commit()
                
                flash('Produit désactivé avec succès', 'success')
                logger.info(f"Produit désactivé: ID {produit_id} par utilisateur ID {session['user_id']}")
                return redirect(url_for('produits_liste'))
        except Exception as e:
            flash(f'Erreur lors de la désactivation du produit: {str(e)}', 'danger')
            logger.error(f"Erreur désactivation produit {produit_id}: {str(e)}")
        finally:
            conn.close()
    
    return redirect(url_for('produits_liste'))

@app.route('/produits/exporter', methods=['GET'])
@login_required
@role_required('supervisor')
@log_activity('export_produits')
def produits_exporter():
    """Export de la liste des produits au format Excel."""
    conn = get_db_connection()
    produits = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                sql = """
                SELECT p.*, SUM(s.quantite) as stock_total 
                FROM produits p 
                LEFT JOIN stocks s ON p.id = s.produit_id AND s.actif = 1
                WHERE p.actif = 1
                GROUP BY p.id
                """
                cursor.execute(sql)
                produits = cursor.fetchall()
        except Exception as e:
            flash(f'Erreur lors de l\'export des produits: {str(e)}', 'danger')
            logger.error(f"Erreur export produits: {str(e)}")
        finally:
            conn.close()
    
    if produits:
        # Créer un DataFrame pandas
        df = pd.DataFrame(produits)
        
        # Réorganiser et renommer les colonnes pour l'export
        columns_order = ['id', 'reference', 'nom', 'categorie', 'prix_unitaire', 
                         'tva', 'unite_mesure', 'stock_total', 'date_creation']
        rename_dict = {
            'id': 'ID',
            'reference': 'Référence',
            'nom': 'Nom',
            'categorie': 'Catégorie',
            'prix_unitaire': 'Prix unitaire',
            'tva': 'TVA (%)',
            'unite_mesure': 'Unité',
            'stock_total': 'Stock total',
            'date_creation': 'Date création'
        }
        
        # Sélectionner et renommer les colonnes
        df = df[[col for col in columns_order if col in df.columns]]
        df = df.rename(columns=rename_dict)
        
        # Créer un buffer pour stocker le fichier Excel
        output = io.BytesIO()
        
        # Créer le fichier Excel
        with pd.ExcelWriter(output, engine='xlsxwriter') as writer:
            df.to_excel(writer, sheet_name='Produits', index=False)
            
            # Formater le document Excel
            workbook = writer.book
            worksheet = writer.sheets['Produits']
            
            # Formats
            header_format = workbook.add_format({
                'bold': True,
                'text_wrap': True,
                'valign': 'top',
                'fg_color': '#D7E4BC',
                'border': 1
            })
            
            # Appliquer le format d'en-tête
            for col_num, value in enumerate(df.columns.values):
                worksheet.write(0, col_num, value, header_format)
                
            # Ajuster la largeur des colonnes
            for i, col in enumerate(df.columns):
                column_width = max(df[col].astype(str).map(len).max(), len(col)) + 2
                worksheet.set_column(i, i, column_width)
        
        # Préparer le fichier pour le téléchargement
        output.seek(0)
        
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        return send_file(
            output,
            as_attachment=True,
            download_name=f'produits_{timestamp}.xlsx',
            mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet'
        )
    
    flash('Aucun produit à exporter', 'warning')
    return redirect(url_for('produits_liste'))

@app.route('/produits/importer', methods=['GET', 'POST'])
@login_required
@role_required('manager')
@log_activity('import_produits')
def produits_importer():
    """Import de produits à partir d'un fichier Excel."""
    if request.method == 'POST':
        if 'fichier' not in request.files:
            flash('Aucun fichier sélectionné', 'danger')
            return redirect(request.url)
        
        file = request.files['fichier']
        if file.filename == '':
            flash('Aucun fichier sélectionné', 'danger')
            return redirect(request.url)
        
        if file and '.' in file.filename and file.filename.rsplit('.', 1)[1].lower() in ['xlsx', 'csv']:
            try:
                # Lire le fichier Excel
                if file.filename.endswith('.xlsx'):
                    df = pd.read_excel(file)
                else:  # CSV
                    df = pd.read_csv(file)
                
                # Vérifier les colonnes requises
                required_columns = ['Référence', 'Nom', 'Catégorie', 'Prix unitaire']
                missing_columns = [col for col in required_columns if col not in df.columns]
                
                if missing_columns:
                    flash(f'Colonnes manquantes dans le fichier: {", ".join(missing_columns)}', 'danger')
                    return redirect(request.url)
                
                # Prétraitement
                df = df.fillna('')
                
                # Récupérer les références existantes
                conn = get_db_connection()
                existing_refs = []
                
                if conn:
                    try:
                        with conn.cursor() as cursor:
                            cursor.execute("SELECT reference FROM produits WHERE actif = 1")
                            results = cursor.fetchall()
                            existing_refs = [result['reference'] for result in results]
                            
                            # Préparer les données pour l'insertion
                            produits_importes = 0
                            produits_mis_a_jour = 0
                            errors = []
                            
                            for index, row in df.iterrows():
                                try:
                                    # Normaliser les données
                                    reference = str(row['Référence']).strip()
                                    nom = str(row['Nom']).strip()
                                    categorie = str(row['Catégorie']).strip()
                                    prix_unitaire = float(row['Prix unitaire'])
                                    
                                    # Valeurs optionnelles
                                    tva = float(row.get('TVA (%)', 19))
                                    unite_mesure = str(row.get('Unité', 'unité')).strip()
                                    description = str(row.get('Description', '')).strip()
                                    
                                    if reference in existing_refs:
                                        # Mise à jour du produit existant
                                        cursor.execute("""
                                            UPDATE produits 
                                            SET nom = %s, description = %s, categorie = %s, 
                                                prix_unitaire = %s, tva = %s, unite_mesure = %s, 
                                                date_modification = %s
                                            WHERE reference = %s AND actif = 1
                                        """, (
                                            nom, description, categorie, 
                                            prix_unitaire, tva, unite_mesure, 
                                            datetime.now(), reference
                                        ))
                                        produits_mis_a_jour += 1
                                    else:
                                        # Insertion d'un nouveau produit
                                        cursor.execute("""
                                            INSERT INTO produits (
                                                reference, nom, description, categorie, 
                                                prix_unitaire, tva, unite_mesure, 
                                                utilisateur_id, date_creation
                                            ) VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                                        """, (
                                            reference, nom, description, categorie,
                                            prix_unitaire, tva, unite_mesure,
                                            session['user_id'], datetime.now()
                                        ))
                                        
                                        # Initialiser le stock
                                        produit_id = cursor.lastrowid
                                        cursor.execute("SELECT id FROM entrepots WHERE actif = 1")
                                        entrepots = cursor.fetchall()
                                        
                                        for entrepot in entrepots:
                                            cursor.execute("""
                                                INSERT INTO stocks (
                                                    produit_id, entrepot_id, quantite, seuil_alerte, 
                                                    utilisateur_id, date_creation
                                                ) VALUES (%s, %s, %s, %s, %s, %s)
                                            """, (
                                                produit_id, entrepot['id'], 0, 10,
                                                session['user_id'], datetime.now()
                                            ))
                                        
                                        existing_refs.append(reference)
                                        produits_importes += 1
                                except Exception as e:
                                    errors.append(f"Ligne {index+2}: {str(e)}")
                            
                            conn.commit()
                            
                            if errors:
                                flash(f'Import terminé avec {len(errors)} erreurs. Voir les logs pour plus de détails.', 'warning')
                                for error in errors:
                                    logger.error(f"Erreur import produit: {error}")
                            else:
                                flash(f'Import réussi: {produits_importes} produits importés, {produits_mis_a_jour} produits mis à jour', 'success')
                                logger.info(f"Import produits: {produits_importes} importés, {produits_mis_a_jour} mis à jour par utilisateur ID {session['user_id']}")
                            
                            return redirect(url_for('produits_liste'))
                    except Exception as e:
                        flash(f'Erreur lors de l\'import: {str(e)}', 'danger')
                        logger.error(f"Erreur import produits: {str(e)}")
                    finally:
                        conn.close()
            except Exception as e:
                flash(f'Erreur lors de la lecture du fichier: {str(e)}', 'danger')
                logger.error(f"Erreur lecture fichier import: {str(e)}")
        else:
            flash('Format de fichier non supporté. Utilisez .xlsx ou .csv', 'danger')
    
    return render_template('produits/importer.html')





# =============================================================================
# GESTION DES STOCKS
# =============================================================================

@app.route('/stocks')
@login_required
@log_activity('liste_stocks')
def stocks_liste():
    """Liste des stocks par produit et entrepôt."""
    conn = get_db_connection()
    stocks = []
    entrepots = []
    
    # Paramètres de filtrage
    entrepot_id = request.args.get('entrepot_id', type=int)
    categorie = request.args.get('categorie')
    niveau = request.args.get('niveau')  # normal, alerte, critique
    recherche = request.args.get('recherche')
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Liste des entrepôts
                cursor.execute("SELECT * FROM entrepots WHERE actif = 1 ORDER BY nom")
                entrepots = cursor.fetchall()
                
                # Construction de la requête de stocks
                sql = """
                SELECT s.*, p.nom as produit_nom, p.reference, p.categorie, e.nom as entrepot_nom
                FROM stocks s
                JOIN produits p ON s.produit_id = p.id
                JOIN entrepots e ON s.entrepot_id = e.id
                WHERE s.actif = 1 AND p.actif = 1
                """
                params = []
                
                # Appliquer les filtres
                if entrepot_id:
                    sql += " AND s.entrepot_id = %s"
                    params.append(entrepot_id)
                
                if categorie:
                    sql += " AND p.categorie = %s"
                    params.append(categorie)
                
                if niveau == 'alerte':
                    sql += " AND s.quantite <= s.seuil_alerte AND s.quantite > (s.seuil_alerte * 0.5)"
                elif niveau == 'critique':
                    sql += " AND s.quantite <= (s.seuil_alerte * 0.5)"
                elif niveau == 'rupture':
                    sql += " AND s.quantite = 0"
                elif niveau == 'normal':
                    sql += " AND s.quantite > s.seuil_alerte"
                
                if recherche:
                    sql += " AND (p.nom LIKE %s OR p.reference LIKE %s)"
                    params.extend([f'%{recherche}%', f'%{recherche}%'])
                
                # Tri par défaut
                sql += " ORDER BY p.nom, e.nom"
                
                cursor.execute(sql, params)
                stocks = cursor.fetchall()
                
                # Catégories pour le filtre
                cursor.execute("SELECT DISTINCT categorie FROM produits WHERE actif = 1 ORDER BY categorie")
                categories = cursor.fetchall()
                
                # Ajouter indicateur de statut
                for stock in stocks:
                    if stock['quantite'] == 0:
                        stock['statut'] = 'rupture'
                        stock['classe_statut'] = 'danger'
                    elif stock['quantite'] <= stock['seuil_alerte'] * 0.5:
                        stock['statut'] = 'critique'
                        stock['classe_statut'] = 'danger'
                    elif stock['quantite'] <= stock['seuil_alerte']:
                        stock['statut'] = 'alerte'
                        stock['classe_statut'] = 'warning'
                    else:
                        stock['statut'] = 'normal'
                        stock['classe_statut'] = 'success'
        except Exception as e:
            flash(f'Erreur lors de la récupération des stocks: {str(e)}', 'danger')
            logger.error(f"Erreur liste stocks: {str(e)}")
        finally:
            conn.close()
    
    return render_template('stocks/liste.html', 
                          stocks=stocks, 
                          entrepots=entrepots,
                          categories=categories if 'categories' in locals() else [],
                          filtres={
                              'entrepot_id': entrepot_id,
                              'categorie': categorie,
                              'niveau': niveau,
                              'recherche': recherche
                          })

@app.route('/stocks/mouvement', methods=['GET', 'POST'])
@login_required
@role_required('operator')
@log_activity('mouvement_stock')
def stock_mouvement():
    """Enregistrement d'un mouvement de stock (entrée ou sortie)."""
    conn = get_db_connection()
    produits = []
    entrepots = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Liste des produits
                cursor.execute("""
                    SELECT p.id, p.nom, p.reference 
                    FROM produits p
                    WHERE p.actif = 1
                    ORDER BY p.nom
                """)
                produits = cursor.fetchall()
                
                # Liste des entrepôts
                cursor.execute("SELECT id, nom FROM entrepots WHERE actif = 1 ORDER BY nom")
                entrepots = cursor.fetchall()
                
                if request.method == 'POST':
                    produit_id = request.form.get('produit_id')
                    entrepot_id = request.form.get('entrepot_id')
                    type_mouvement = request.form.get('type_mouvement')
                    quantite = int(request.form.get('quantite'))
                    commentaire = request.form.get('commentaire')
                    
                    # Vérifier la validité des données
                    if quantite <= 0:
                        flash('La quantité doit être supérieure à zéro', 'danger')
                        return render_template('stocks/mouvement.html', produits=produits, entrepots=entrepots)
                    
                    # Vérifier si le stock existe pour ce produit/entrepôt
                    cursor.execute("""
                        SELECT * FROM stocks 
                        WHERE produit_id = %s AND entrepot_id = %s AND actif = 1
                    """, (produit_id, entrepot_id))
                    stock = cursor.fetchone()
                    
                    if not stock:
                        # Créer le stock s'il n'existe pas
                        cursor.execute("""
                            INSERT INTO stocks (produit_id, entrepot_id, quantite, seuil_alerte, 
                                               utilisateur_id, date_creation)
                            VALUES (%s, %s, 0, 10, %s, %s)
                        """, (produit_id, entrepot_id, session['user_id'], datetime.now()))
                        conn.commit()
                        
                        # Récupérer le stock créé
                        cursor.execute("""
                            SELECT * FROM stocks 
                            WHERE produit_id = %s AND entrepot_id = %s AND actif = 1
                        """, (produit_id, entrepot_id))
                        stock = cursor.fetchone()
                    
                    # Mettre à jour le stock
                    if type_mouvement == 'entree':
                        cursor.execute("""
                            UPDATE stocks 
                            SET quantite = quantite + %s, date_modification = %s
                            WHERE id = %s
                        """, (quantite, datetime.now(), stock['id']))
                    else:  # sortie
                        # Vérifier si le stock est suffisant
                        if stock['quantite'] < quantite:
                            flash('Stock insuffisant pour effectuer cette sortie', 'danger')
                            return render_template('stocks/mouvement.html', produits=produits, entrepots=entrepots)
                        
                        cursor.execute("""
                            UPDATE stocks 
                            SET quantite = quantite - %s, date_modification = %s
                            WHERE id = %s
                        """, (quantite, datetime.now(), stock['id']))
                    
                    # Enregistrer le mouvement de stock
                    cursor.execute("""
                        INSERT INTO mouvements_stock 
                        (produit_id, entrepot_id, type_mouvement, quantite, commentaire, 
                        utilisateur_id, date_mouvement)
                        VALUES (%s, %s, %s, %s, %s, %s, %s)
                    """, (
                        produit_id, entrepot_id, type_mouvement, quantite, 
                        commentaire, session['user_id'], datetime.now()
                    ))
                    
                    conn.commit()
                    
                    # Récupérer les infos du produit pour le log
                    cursor.execute("SELECT nom, reference FROM produits WHERE id = %s", (produit_id,))
                    produit_info = cursor.fetchone()
                    cursor.execute("SELECT nom FROM entrepots WHERE id = %s", (entrepot_id,))
                    entrepot_info = cursor.fetchone()
                    
                    log_message = f"Mouvement stock: {type_mouvement} de {quantite} unités pour {produit_info['nom']} ({produit_info['reference']}) à {entrepot_info['nom']}"
                    flash('Mouvement de stock enregistré avec succès', 'success')
                    logger.info(log_message)
                    
                    # Vérifier si le stock est bas après le mouvement
                    if type_mouvement == 'sortie':
                        cursor.execute("""
                            SELECT s.*, p.nom as produit_nom, p.reference, e.nom as entrepot_nom
                            FROM stocks s
                            JOIN produits p ON s.produit_id = p.id
                            JOIN entrepots e ON s.entrepot_id = e.id
                            WHERE s.id = %s AND s.quantite <= s.seuil_alerte
                        """, (stock['id'],))
                        stock_alerte = cursor.fetchone()
                        
                        if stock_alerte:
                            alerte_message = f"Stock bas: {stock_alerte['produit_nom']} ({stock_alerte['reference']}) - {stock_alerte['quantite']}/{stock_alerte['seuil_alerte']} à {stock_alerte['entrepot_nom']}"
                            flash(alerte_message, 'warning')
                    
                    return redirect(url_for('stocks_liste'))
                
        except Exception as e:
            flash(f'Erreur lors du mouvement de stock: {str(e)}', 'danger')
            logger.error(f"Erreur mouvement stock: {str(e)}")
        finally:
            conn.close()
    
    return render_template('stocks/mouvement.html', produits=produits, entrepots=entrepots)

@app.route('/stocks/inventaire', methods=['GET', 'POST'])
@login_required
@role_required('supervisor')
@log_activity('inventaire_stock')
def stock_inventaire():
    """Réalisation d'un inventaire physique des stocks."""
    conn = get_db_connection()
    stocks = []
    entrepot_id = request.args.get('entrepot_id', 1, type=int)
    categorie = request.args.get('categorie')
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Liste des entrepôts
                cursor.execute("SELECT id, nom FROM entrepots WHERE actif = 1 ORDER BY nom")
                entrepots = cursor.fetchall()
                
                # Liste des catégories
                cursor.execute("SELECT DISTINCT categorie FROM produits WHERE actif = 1 ORDER BY categorie")
                categories = cursor.fetchall()
                
                # Construire la requête pour les stocks de l'entrepôt sélectionné
                sql = """
                SELECT s.*, p.nom as produit_nom, p.reference, p.categorie
                FROM stocks s
                JOIN produits p ON s.produit_id = p.id
                WHERE s.entrepot_id = %s AND s.actif = 1 AND p.actif = 1
                """
                params = [entrepot_id]
                
                if categorie:
                    sql += " AND p.categorie = %s"
                    params.append(categorie)
                
                sql += " ORDER BY p.nom"
                cursor.execute(sql, params)
                stocks = cursor.fetchall()
                
                if request.method == 'POST':
                    # Initialiser le journal d'inventaire
                    cursor.execute("""
                        INSERT INTO journaux_inventaire 
                        (entrepot_id, utilisateur_id, date_creation, commentaire)
                        VALUES (%s, %s, %s, %s)
                    """, (
                        entrepot_id, 
                        session['user_id'], 
                        datetime.now(),
                        request.form.get('commentaire', '')
                    ))
                    journal_id = cursor.lastrowid
                    
                    # Traiter les stocks un par un
                    mouvements = []
                    for key, value in request.form.items():
                        if key.startswith('stock_'):
                            stock_id = int(key.split('_')[1])
                            if value.strip():  # Ignorer les valeurs vides
                                try:
                                    nouvelle_quantite = int(value)
                                    
                                    # Récupérer les informations actuelles du stock
                                    cursor.execute("""
                                        SELECT s.quantite, s.produit_id, p.nom as produit_nom, p.reference
                                        FROM stocks s
                                        JOIN produits p ON s.produit_id = p.id
                                        WHERE s.id = %s
                                    """, (stock_id,))
                                    stock_actuel = cursor.fetchone()
                                    
                                    if stock_actuel:
                                        diff = nouvelle_quantite - stock_actuel['quantite']
                                        
                                        # Enregistrer la ligne d'inventaire
                                        cursor.execute("""
                                            INSERT INTO lignes_inventaire 
                                            (journal_id, produit_id, stock_id, quantite_avant, 
                                            quantite_apres, difference, date_creation)
                                            VALUES (%s, %s, %s, %s, %s, %s, %s)
                                        """, (
                                            journal_id,
                                            stock_actuel['produit_id'],
                                            stock_id,
                                            stock_actuel['quantite'],
                                            nouvelle_quantite,
                                            diff,
                                            datetime.now()
                                        ))
                                        
                                        # Mettre à jour le stock
                                        cursor.execute("""
                                            UPDATE stocks 
                                            SET quantite = %s, date_modification = %s
                                            WHERE id = %s
                                        """, (nouvelle_quantite, datetime.now(), stock_id))
                                        
                                        # Déterminer le type de mouvement
                                        type_mouvement = 'inventaire_plus' if diff >= 0 else 'inventaire_moins'
                                        commentaire = f"Ajustement inventaire du {datetime.now().strftime('%d/%m/%Y')}"
                                        
                                        # Enregistrer le mouvement d'inventaire
                                        cursor.execute("""
                                            INSERT INTO mouvements_stock 
                                            (produit_id, entrepot_id, type_mouvement, quantite, commentaire, 
                                            utilisateur_id, date_mouvement, journal_inventaire_id)
                                            VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                                        """, (
                                            stock_actuel['produit_id'], 
                                            entrepot_id, 
                                            type_mouvement, 
                                            abs(diff), 
                                            commentaire, 
                                            session['user_id'], 
                                            datetime.now(),
                                            journal_id
                                        ))
                                        
                                        # Enregistrer les mouvements pour le résumé
                                        if diff != 0:
                                            mouvements.append({
                                                'produit': stock_actuel['produit_nom'],
                                                'reference': stock_actuel['reference'],
                                                'avant': stock_actuel['quantite'],
                                                'apres': nouvelle_quantite,
                                                'diff': diff
                                            })
                                except ValueError:
                                    # Ignorer les valeurs non numériques
                                    pass
                    
                    conn.commit()
                    
                    # Enregistrer un résumé de l'inventaire dans les logs
                    ajustements = len(mouvements)
                    if ajustements > 0:
                        logger.info(f"Inventaire réalisé pour entrepôt ID {entrepot_id}: {ajustements} ajustements")
                        for mouvement in mouvements[:10]:  # Limiter à 10 pour les logs
                            logger.info(f"Ajustement: {mouvement['produit']} ({mouvement['reference']}): {mouvement['avant']} -> {mouvement['apres']} ({mouvement['diff']})")
                    else:
                        logger.info(f"Inventaire réalisé pour entrepôt ID {entrepot_id}: aucun ajustement")
                    
                    flash(f'Inventaire mis à jour avec succès. {ajustements} produits ajustés.', 'success')
                    return redirect(url_for('stocks_liste'))
                
        except Exception as e:
            flash(f'Erreur lors de l\'inventaire: {str(e)}', 'danger')
            logger.error(f"Erreur inventaire: {str(e)}")
        finally:
            conn.close()
    
    return render_template('stocks/inventaire.html', 
                          stocks=stocks, 
                          entrepots=entrepots if 'entrepots' in locals() else [],
                          categories=categories if 'categories' in locals() else [],
                          entrepot_id=entrepot_id, 
                          categorie=categorie)

@app.route('/stocks/historique')
@login_required
@log_activity('historique_stock')
def stock_historique():
    """Historique des mouvements de stock."""
    conn = get_db_connection()
    mouvements = []
    
    # Paramètres de filtrage
    produit_id = request.args.get('produit_id', type=int)
    entrepot_id = request.args.get('entrepot_id', type=int)
    type_mouvement = request.args.get('type_mouvement')
    utilisateur_id = request.args.get('utilisateur_id', type=int)
    date_debut = request.args.get('date_debut', (datetime.now() - timedelta(days=30)).strftime('%Y-%m-%d'))
    date_fin = request.args.get('date_fin', datetime.now().strftime('%Y-%m-%d'))
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Listes pour les filtres
                cursor.execute("SELECT id, nom, reference FROM produits WHERE actif = 1 ORDER BY nom")
                produits = cursor.fetchall()
                
                cursor.execute("SELECT id, nom FROM entrepots WHERE actif = 1 ORDER BY nom")
                entrepots = cursor.fetchall()
                
                cursor.execute("SELECT id, CONCAT(prenom, ' ', nom) as nom_complet FROM utilisateurs WHERE actif = 1 ORDER BY nom")
                utilisateurs = cursor.fetchall()
                
                # Construire la requête
                sql = """
                SELECT m.*, p.nom as produit_nom, p.reference, e.nom as entrepot_nom,
                       u.prenom, u.nom as nom_utilisateur
                FROM mouvements_stock m
                JOIN produits p ON m.produit_id = p.id
                JOIN entrepots e ON m.entrepot_id = e.id
                JOIN utilisateurs u ON m.utilisateur_id = u.id
                WHERE m.date_mouvement BETWEEN %s AND %s
                """
                params = [f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"]
                
                # Ajouter les filtres
                if produit_id:
                    sql += " AND m.produit_id = %s"
                    params.append(produit_id)
                
                if entrepot_id:
                    sql += " AND m.entrepot_id = %s"
                    params.append(entrepot_id)
                
                if type_mouvement:
                    sql += " AND m.type_mouvement = %s"
                    params.append(type_mouvement)
                
                if utilisateur_id:
                    sql += " AND m.utilisateur_id = %s"
                    params.append(utilisateur_id)
                
                # Tri et limite
                sql += " ORDER BY m.date_mouvement DESC LIMIT 1000"
                
                cursor.execute(sql, params)
                mouvements = cursor.fetchall()
                
                # Formater les types de mouvement pour l'affichage
                for m in mouvements:
                    if m['type_mouvement'] == 'entree':
                        m['type_affichage'] = 'Entrée'
                        m['classe_type'] = 'success'
                    elif m['type_mouvement'] == 'sortie':
                        m['type_affichage'] = 'Sortie'
                        m['classe_type'] = 'danger'
                    elif m['type_mouvement'] == 'production':
                        m['type_affichage'] = 'Production'
                        m['classe_type'] = 'info'
                    elif m['type_mouvement'] == 'inventaire_plus':
                        m['type_affichage'] = 'Inventaire +'
                        m['classe_type'] = 'primary'
                    elif m['type_mouvement'] == 'inventaire_moins':
                        m['type_affichage'] = 'Inventaire -'
                        m['classe_type'] = 'warning'
                    else:
                        m['type_affichage'] = m['type_mouvement'].capitalize()
                        m['classe_type'] = 'secondary'
                
        except Exception as e:
            flash(f'Erreur lors de la récupération de l\'historique: {str(e)}', 'danger')
            logger.error(f"Erreur historique stock: {str(e)}")
        finally:
            conn.close()
    
    return render_template('stocks/historique.html', 
                          mouvements=mouvements,
                          produits=produits if 'produits' in locals() else [],
                          entrepots=entrepots if 'entrepots' in locals() else [],
                          utilisateurs=utilisateurs if 'utilisateurs' in locals() else [],
                          types_mouvement=[
                              {'code': 'entree', 'nom': 'Entrée'},
                              {'code': 'sortie', 'nom': 'Sortie'},
                              {'code': 'production', 'nom': 'Production'},
                              {'code': 'inventaire_plus', 'nom': 'Inventaire +'},
                              {'code': 'inventaire_moins', 'nom': 'Inventaire -'}
                          ],
                          filtres={
                              'produit_id': produit_id,
                              'entrepot_id': entrepot_id,
                              'type_mouvement': type_mouvement,
                              'utilisateur_id': utilisateur_id,
                              'date_debut': date_debut,
                              'date_fin': date_fin
                          })

@app.route('/stocks/transfert', methods=['GET', 'POST'])
@login_required
@role_required('operator')
@log_activity('transfert_stock')
def stock_transfert():
    """Transfert de stock entre entrepôts."""
    conn = get_db_connection()
    produits = []
    entrepots = []
    stocks_disponibles = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Liste des produits
                cursor.execute("""
                    SELECT DISTINCT p.id, p.nom, p.reference 
                    FROM produits p
                    JOIN stocks s ON p.id = s.produit_id
                    WHERE p.actif = 1 AND s.actif = 1 AND s.quantite > 0
                    ORDER BY p.nom
                """)
                produits = cursor.fetchall()
                
                # Liste des entrepôts
                cursor.execute("SELECT id, nom FROM entrepots WHERE actif = 1 ORDER BY nom")
                entrepots = cursor.fetchall()
                
                # Si produit sélectionné, récupérer les stocks disponibles
                produit_id = request.args.get('produit_id', type=int)
                if produit_id:
                    cursor.execute("""
                        SELECT s.*, e.nom as entrepot_nom
                        FROM stocks s
                        JOIN entrepots e ON s.entrepot_id = e.id
                        WHERE s.produit_id = %s AND s.actif = 1 AND s.quantite > 0
                        ORDER BY e.nom
                    """, (produit_id,))
                    stocks_disponibles = cursor.fetchall()
                
                if request.method == 'POST':
                    produit_id = request.form.get('produit_id', type=int)
                    entrepot_source_id = request.form.get('entrepot_source_id', type=int)
                    entrepot_destination_id = request.form.get('entrepot_destination_id', type=int)
                    quantite = request.form.get('quantite', type=int)
                    commentaire = request.form.get('commentaire', '')
                    
                    # Validation
                    if not produit_id or not entrepot_source_id or not entrepot_destination_id or not quantite:
                        flash('Tous les champs sont obligatoires', 'danger')
                        return redirect(url_for('stock_transfert'))
                    
                    if entrepot_source_id == entrepot_destination_id:
                        flash('Les entrepôts source et destination doivent être différents', 'danger')
                        return redirect(url_for('stock_transfert'))
                    
                    if quantite <= 0:
                        flash('La quantité doit être supérieure à zéro', 'danger')
                        return redirect(url_for('stock_transfert'))
                    
                    # Vérifier le stock disponible
                    cursor.execute("""
                        SELECT * FROM stocks 
                        WHERE produit_id = %s AND entrepot_id = %s AND actif = 1
                    """, (produit_id, entrepot_source_id))
                    stock_source = cursor.fetchone()
                    
                    if not stock_source or stock_source['quantite'] < quantite:
                        flash('Stock insuffisant dans l\'entrepôt source', 'danger')
                        return redirect(url_for('stock_transfert'))
                    
                    # Vérifier si le stock destination existe
                    cursor.execute("""
                        SELECT * FROM stocks 
                        WHERE produit_id = %s AND entrepot_id = %s AND actif = 1
                    """, (produit_id, entrepot_destination_id))
                    stock_destination = cursor.fetchone()
                    
                    if not stock_destination:
                        # Créer le stock destination
                        cursor.execute("""
                            INSERT INTO stocks (produit_id, entrepot_id, quantite, seuil_alerte, 
                                              utilisateur_id, date_creation)
                            VALUES (%s, %s, 0, %s, %s, %s)
                        """, (
                            produit_id, 
                            entrepot_destination_id, 
                            stock_source['seuil_alerte'],  # Copier le même seuil d'alerte
                            session['user_id'], 
                            datetime.now()
                        ))
                        conn.commit()
                        
                        # Récupérer le nouveau stock
                        cursor.execute("""
                            SELECT * FROM stocks 
                            WHERE produit_id = %s AND entrepot_id = %s AND actif = 1
                        """, (produit_id, entrepot_destination_id))
                        stock_destination = cursor.fetchone()
                    
                    # Démarrer une transaction pour s'assurer de l'intégrité
                    conn.begin()
                    
                    try:
                        # Décrémenter le stock source
                        cursor.execute("""
                            UPDATE stocks 
                            SET quantite = quantite - %s, date_modification = %s
                            WHERE id = %s
                        """, (quantite, datetime.now(), stock_source['id']))
                        
                        # Incrémenter le stock destination
                        cursor.execute("""
                            UPDATE stocks 
                            SET quantite = quantite + %s, date_modification = %s
                            WHERE id = %s
                        """, (quantite, datetime.now(), stock_destination['id']))
                        
                        # Enregistrer les mouvements
                        # 1. Sortie du stock source
                        cursor.execute("""
                            INSERT INTO mouvements_stock 
                            (produit_id, entrepot_id, type_mouvement, quantite, commentaire, 
                            utilisateur_id, date_mouvement, transfert_id)
                            VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                        """, (
                            produit_id, 
                            entrepot_source_id, 
                            'transfert_sortie', 
                            quantite, 
                            f"Transfert vers {entrepot_destination_id}: {commentaire}", 
                            session['user_id'], 
                            datetime.now(),
                            uuid.uuid4().hex  # ID unique pour lier les deux mouvements du transfert
                        ))
                        
                        transfert_id = cursor.lastrowid
                        
                        # 2. Entrée dans le stock destination
                        cursor.execute("""
                            INSERT INTO mouvements_stock 
                            (produit_id, entrepot_id, type_mouvement, quantite, commentaire, 
                            utilisateur_id, date_mouvement, transfert_id, mouvement_lie_id)
                            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                        """, (
                            produit_id, 
                            entrepot_destination_id, 
                            'transfert_entree', 
                            quantite, 
                            f"Transfert depuis {entrepot_source_id}: {commentaire}", 
                            session['user_id'], 
                            datetime.now(),
                            uuid.uuid4().hex,
                            transfert_id
                        ))
                        
                        # Valider la transaction
                        conn.commit()
                        
                        # Récupérer les noms pour le log
                        cursor.execute("SELECT nom, reference FROM produits WHERE id = %s", (produit_id,))
                        produit_info = cursor.fetchone()
                        cursor.execute("SELECT nom FROM entrepots WHERE id = %s", (entrepot_source_id,))
                        source_info = cursor.fetchone()
                        cursor.execute("SELECT nom FROM entrepots WHERE id = %s", (entrepot_destination_id,))
                        destination_info = cursor.fetchone()
                        
                        log_message = f"Transfert de {quantite} {produit_info['nom']} ({produit_info['reference']}) de {source_info['nom']} vers {destination_info['nom']}"
                        flash('Transfert effectué avec succès', 'success')
                        logger.info(log_message)
                        
                        return redirect(url_for('stocks_liste'))
                    
                    except Exception as e:
                        # En cas d'erreur, annuler la transaction
                        conn.rollback()
                        raise e
                
        except Exception as e:
            flash(f'Erreur lors du transfert de stock: {str(e)}', 'danger')
            logger.error(f"Erreur transfert stock: {str(e)}")
        finally:
            conn.close()
    
    return render_template('stocks/transfert.html', 
                          produits=produits, 
                          entrepots=entrepots,
                          stocks_disponibles=stocks_disponibles,
                          produit_id=produit_id if 'produit_id' in locals() else None)

@app.route('/stocks/rapport')
@login_required
@role_required('supervisor')
@log_activity('rapport_stock')
def stock_rapport():
    """Génération de rapports d'analyse des stocks."""
    conn = get_db_connection()
    statistiques = {}
    graphiques = {}
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Statistiques globales
                cursor.execute("""
                    SELECT COUNT(DISTINCT s.produit_id) as nb_produits,
                           COUNT(DISTINCT s.entrepot_id) as nb_entrepots,
                           SUM(s.quantite) as stock_total,
                           SUM(CASE WHEN s.quantite <= s.seuil_alerte THEN 1 ELSE 0 END) as nb_alertes,
                           SUM(CASE WHEN s.quantite = 0 THEN 1 ELSE 0 END) as nb_ruptures
                    FROM stocks s
                    WHERE s.actif = 1
                """)
                statistiques['global'] = cursor.fetchone()
                
                # Stocks par catégorie
                cursor.execute("""
                    SELECT p.categorie, 
                           COUNT(DISTINCT s.produit_id) as nb_produits,
                           SUM(s.quantite) as stock_total
                    FROM stocks s
                    JOIN produits p ON s.produit_id = p.id
                    WHERE s.actif = 1 AND p.actif = 1
                    GROUP BY p.categorie
                    ORDER BY stock_total DESC
                """)
                statistiques['categories'] = cursor.fetchall()
                
                # Top 10 produits à faible stock
                cursor.execute("""
                    SELECT s.*, p.nom as produit_nom, p.reference, p.categorie,
                           e.nom as entrepot_nom,
                           (s.quantite / s.seuil_alerte) * 100 as pourcentage_seuil
                    FROM stocks s
                    JOIN produits p ON s.produit_id = p.id
                    JOIN entrepots e ON s.entrepot_id = e.id
                    WHERE s.actif = 1 AND p.actif = 1 AND s.quantite <= s.seuil_alerte
                    ORDER BY pourcentage_seuil ASC
                    LIMIT 10
                """)
                statistiques['stock_bas'] = cursor.fetchall()
                
                # Analyse de mouvements (30 derniers jours)
                cursor.execute("""
                    SELECT DATE_FORMAT(date_mouvement, '%Y-%m-%d') as date,
                           SUM(CASE WHEN type_mouvement IN ('entree', 'production', 'transfert_entree', 'inventaire_plus') 
                                THEN quantite ELSE 0 END) as entrees,
                           SUM(CASE WHEN type_mouvement IN ('sortie', 'transfert_sortie', 'inventaire_moins') 
                                THEN quantite ELSE 0 END) as sorties
                    FROM mouvements_stock
                    WHERE date_mouvement >= DATE_SUB(CURDATE(), INTERVAL 30 DAY)
                    GROUP BY date
                    ORDER BY date
                """)
                mouvements_data = cursor.fetchall()
                
                # Graphique des stocks par catégorie
                if statistiques['categories']:
                    plt.figure(figsize=(10, 6))
                    categories = [c['categorie'] for c in statistiques['categories']]
                    stocks = [c['stock_total'] for c in statistiques['categories']]
                    
                    plt.bar(categories, stocks)
                    plt.title('Stock total par catégorie de produit')
                    plt.xlabel('Catégorie')
                    plt.ylabel('Quantité en stock')
                    plt.xticks(rotation=45)
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    graphiques['stocks_categories'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
                # Graphique des mouvements de stock
                if mouvements_data:
                    plt.figure(figsize=(12, 6))
                    dates = [m['date'] for m in mouvements_data]
                    entrees = [m['entrees'] for m in mouvements_data]
                    sorties = [m['sorties'] for m in mouvements_data]
                    
                    plt.plot(dates, entrees, 'g-', label='Entrées')
                    plt.plot(dates, sorties, 'r-', label='Sorties')
                    plt.title('Mouvements de stock (30 derniers jours)')
                    plt.xlabel('Date')
                    plt.ylabel('Quantité')
                    plt.legend()
                    plt.grid(True, linestyle='--', alpha=0.7)
                    plt.xticks(rotation=45)
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    graphiques['mouvements'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
                # Graphique des alertes de stock
                if statistiques['stock_bas']:
                    plt.figure(figsize=(12, 6))
                    produits = [f"{s['produit_nom']} ({s['reference']})" for s in statistiques['stock_bas']]
                    quantites = [s['quantite'] for s in statistiques['stock_bas']]
                    seuils = [s['seuil_alerte'] for s in statistiques['stock_bas']]
                    
                    plt.barh(produits, quantites, color='red', alpha=0.7, label='Stock actuel')
                    plt.barh(produits, seuils, color='blue', alpha=0.3, label='Seuil d\'alerte')
                    
                    plt.title('Produits en alerte de stock')
                    plt.xlabel('Quantité')
                    plt.ylabel('Produit')
                    plt.legend()
                    plt.grid(True, linestyle='--', alpha=0.7)
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    graphiques['alertes'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
        except Exception as e:
            flash(f'Erreur lors de la génération du rapport: {str(e)}', 'danger')
            logger.error(f"Erreur rapport stock: {str(e)}")
        finally:
            conn.close()
    
    return render_template('stocks/rapport.html', 
                          statistiques=statistiques, 
                          graphiques=graphiques)

# =============================================================================
# GESTION DE LA PRODUCTION
# =============================================================================

@app.route('/production')
@login_required
@log_activity('liste_production')
def production_liste():
    """Liste des productions réalisées."""
    conn = get_db_connection()
    productions = []
    
    # Paramètres de filtrage
    page = request.args.get('page', 1, type=int)
    per_page = request.args.get('per_page', 20, type=int)
    produit_id = request.args.get('produit_id', type=int)
    ligne_id = request.args.get('ligne_id', type=int)
    date_debut = request.args.get('date_debut')
    date_fin = request.args.get('date_fin')
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Listes pour les filtres
                cursor.execute("SELECT id, nom, reference FROM produits WHERE actif = 1 ORDER BY nom")
                produits = cursor.fetchall()
                
                cursor.execute("SELECT id, nom FROM lignes_production WHERE actif = 1 ORDER BY nom")
                lignes = cursor.fetchall()
                
                # Construction de la requête
                sql = """
                SELECT p.*, pr.nom as produit_nom, pr.reference, l.nom as ligne_nom,
                       u.prenom, u.nom as nom_utilisateur
                FROM production p
                JOIN produits pr ON p.produit_id = pr.id
                JOIN lignes_production l ON p.ligne_production_id = l.id
                JOIN utilisateurs u ON p.utilisateur_id = u.id
                WHERE 1=1
                """
                params = []
                
                # Ajout des filtres
                if produit_id:
                    sql += " AND p.produit_id = %s"
                    params.append(produit_id)
                
                if ligne_id:
                    sql += " AND p.ligne_production_id = %s"
                    params.append(ligne_id)
                
                if date_debut:
                    sql += " AND p.date_creation >= %s"
                    params.append(f"{date_debut} 00:00:00")
                
                if date_fin:
                    sql += " AND p.date_creation <= %s"
                    params.append(f"{date_fin} 23:59:59")
                
                # Compter le nombre total d'enregistrements pour la pagination
                count_sql = f"SELECT COUNT(*) as total FROM ({sql}) as subquery"
                cursor.execute(count_sql, params)
                total_count = cursor.fetchone()['total']
                
                # Ajouter tri et pagination
                sql += " ORDER BY p.date_creation DESC LIMIT %s OFFSET %s"
                params.extend([per_page, (page - 1) * per_page])
                
                cursor.execute(sql, params)
                productions = cursor.fetchall()
                
                # Calculer la pagination
                total_pages = (total_count + per_page - 1) // per_page
                pagination = {
                    'page': page,
                    'per_page': per_page,
                    'total_count': total_count,
                    'total_pages': total_pages
                }
                
                # Ajouter les calculs de productivité
                for p in productions:
                    if p['temps_production'] > 0:
                        p['productivite'] = round(p['quantite_produite'] / p['temps_production'], 2)
                    else:
                        p['productivite'] = 0
        except Exception as e:
            flash(f'Erreur lors de la récupération des productions: {str(e)}', 'danger')
            logger.error(f"Erreur liste production: {str(e)}")
        finally:
            conn.close()
    
    return render_template('production/liste.html', 
                          productions=productions,
                          produits=produits if 'produits' in locals() else [],
                          lignes=lignes if 'lignes' in locals() else [],
                          pagination=pagination if 'pagination' in locals() else {},
                          filtres={
                              'produit_id': produit_id,
                              'ligne_id': ligne_id,
                              'date_debut': date_debut,
                              'date_fin': date_fin
                          })

@app.route('/production/ajouter', methods=['GET', 'POST'])
@login_required
@role_required('operator')
@log_activity('ajout_production')
def production_ajouter():
    """Enregistrement d'une nouvelle production."""
    conn = get_db_connection()
    produits = []
    lignes = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Liste des produits
                cursor.execute("SELECT id, nom, reference FROM produits WHERE actif = 1 ORDER BY nom")
                produits = cursor.fetchall()
                
                # Liste des lignes de production
                cursor.execute("SELECT id, nom FROM lignes_production WHERE actif = 1 ORDER BY nom")
                lignes = cursor.fetchall()
                
                if request.method == 'POST':
                    produit_id = request.form.get('produit_id')
                    ligne_production_id = request.form.get('ligne_production_id')
                    quantite_produite = request.form.get('quantite_produite')
                    temps_production = request.form.get('temps_production')
                    numero_lot = request.form.get('numero_lot', 'LOT-' + datetime.now().strftime('%Y%m%d-%H%M%S'))
                    commentaire = request.form.get('commentaire')
                    
                    # Validation
                    if not produit_id or not ligne_production_id or not quantite_produite or not temps_production:
                        flash('Tous les champs obligatoires doivent être remplis', 'danger')
                    else:
                        # Enregistrer la production
                        cursor.execute("""
                            INSERT INTO production 
                            (produit_id, ligne_production_id, quantite_produite, temps_production, 
                             numero_lot, commentaire, utilisateur_id, date_creation)
                            VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                        """, (
                            produit_id, ligne_production_id, quantite_produite, temps_production, 
                            numero_lot, commentaire, session['user_id'], datetime.now()
                        ))
                        production_id = cursor.lastrowid
                        
                        # Mettre à jour le stock (ajouter la production au stock)
                        cursor.execute("""
                            SELECT id FROM entrepots WHERE est_production = 1 AND actif = 1 LIMIT 1
                        """)
                        entrepot_production = cursor.fetchone()
                        
                        if entrepot_production:
                            entrepot_id = entrepot_production['id']
                            
                            # Vérifier si le stock existe déjà
                            cursor.execute("""
                                SELECT id FROM stocks 
                                WHERE produit_id = %s AND entrepot_id = %s AND actif = 1
                            """, (produit_id, entrepot_id))
                            stock = cursor.fetchone()
                            
                            if not stock:
                                # Créer le stock avec un seuil d'alerte par défaut
                                cursor.execute("""
                                    INSERT INTO stocks (produit_id, entrepot_id, quantite, seuil_alerte,
                                                      utilisateur_id, date_creation)
                                    VALUES (%s, %s, 0, 10, %s, %s)
                                """, (produit_id, entrepot_id, session['user_id'], datetime.now()))
                                
                                cursor.execute("""
                                    SELECT id FROM stocks 
                                    WHERE produit_id = %s AND entrepot_id = %s AND actif = 1
                                """, (produit_id, entrepot_id))
                                stock = cursor.fetchone()
                            
                            # Ajouter au stock
                            cursor.execute("""
                                UPDATE stocks 
                                SET quantite = quantite + %s, date_modification = %s
                                WHERE id = %s
                            """, (quantite_produite, datetime.now(), stock['id']))
                            
                            # Enregistrer le mouvement de stock
                            cursor.execute("""
                                INSERT INTO mouvements_stock 
                                (produit_id, entrepot_id, type_mouvement, quantite, commentaire,
                                utilisateur_id, date_mouvement, production_id)
                                VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                            """, (
                                produit_id, entrepot_id, 'production', quantite_produite, 
                                f"Production auto: lot {numero_lot}", 
                                session['user_id'], datetime.now(), production_id
                            ))
                        
                        # Récupérer les infos du produit et de la ligne pour le log
                        cursor.execute("SELECT nom, reference FROM produits WHERE id = %s", (produit_id,))
                        produit_info = cursor.fetchone()
                        cursor.execute("SELECT nom FROM lignes_production WHERE id = %s", (ligne_production_id,))
                        ligne_info = cursor.fetchone()
                        
                        conn.commit()
                        
                        log_message = f"Production ajoutée: {quantite_produite} unités de {produit_info['nom']} ({produit_info['reference']}) sur {ligne_info['nom']}"
                        flash('Production enregistrée avec succès', 'success')
                        logger.info(log_message)
                        
                        # Vérifier si la production doit être contrôlée
                        cursor.execute("""
                            SELECT frequence_controle FROM produits WHERE id = %s
                        """, (produit_id,))
                        produit_controle = cursor.fetchone()
                        
                        if produit_controle and produit_controle['frequence_controle'] == 'systematique':
                            flash('Ce produit requiert un contrôle qualité systématique', 'warning')
                        
                        return redirect(url_for('production_liste'))
                
        except Exception as e:
            flash(f'Erreur lors de l\'enregistrement de la production: {str(e)}', 'danger')
            logger.error(f"Erreur ajout production: {str(e)}")
        finally:
            conn.close()
    
    return render_template('production/ajouter.html', produits=produits, lignes=lignes)

@app.route('/production/<int:production_id>')
@login_required
@log_activity('details_production')
def production_details(production_id):
    """Détails d'une production spécifique."""
    conn = get_db_connection()
    production = None
    controles_qualite = []
    details_lot = None
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Informations de la production
                sql = """
                SELECT p.*, pr.nom as produit_nom, pr.reference, pr.description as produit_description,
                       l.nom as ligne_nom, l.description as ligne_description,
                       u.prenom, u.nom as nom_utilisateur
                FROM production p
                JOIN produits pr ON p.produit_id = pr.id
                JOIN lignes_production l ON p.ligne_production_id = l.id
                JOIN utilisateurs u ON p.utilisateur_id = u.id
                WHERE p.id = %s
                """
                cursor.execute(sql, (production_id,))
                production = cursor.fetchone()
                
                if not production:
                    flash('Production non trouvée', 'warning')
                    return redirect(url_for('production_liste'))
                
                # Calcul de la productivité
                if production['temps_production'] > 0:
                    production['productivite'] = round(production['quantite_produite'] / production['temps_production'], 2)
                else:
                    production['productivite'] = 0
                
                # Contrôles qualité associés
                sql = """
                SELECT c.*, u.prenom, u.nom as nom_utilisateur
                FROM controles_qualite c
                JOIN utilisateurs u ON c.utilisateur_id = u.id
                WHERE c.lot_id = %s OR c.numero_lot = %s
                ORDER BY c.date_controle DESC
                """
                cursor.execute(sql, (production_id, production['numero_lot']))
                controles_qualite = cursor.fetchall()
                
                # Formater les résultats des contrôles
                for c in controles_qualite:
                    if c['resultat'] == 'conforme':
                        c['resultat_affichage'] = 'Conforme'
                        c['classe_resultat'] = 'success'
                    elif c['resultat'] == 'non_conforme':
                        c['resultat_affichage'] = 'Non conforme'
                        c['classe_resultat'] = 'danger'
                    else:
                        c['resultat_affichage'] = 'En attente'
                        c['classe_resultat'] = 'warning'
                
                # Détails du lot
                sql = """
                SELECT SUM(c.quantite) as quantite_totale
                FROM mouvements_stock c
                WHERE c.production_id = %s AND c.type_mouvement = 'production'
                """
                cursor.execute(sql, (production_id,))
                details_lot = cursor.fetchone()
                
                # Autres productions du même produit pour comparaison
                sql = """
                SELECT AVG(temps_production) as temps_moyen,
                       AVG(quantite_produite) as quantite_moyenne,
                       AVG(quantite_produite / temps_production) as productivite_moyenne
                FROM production
                WHERE produit_id = %s AND id != %s
                """
                cursor.execute(sql, (production['produit_id'], production_id))
                statistiques_produit = cursor.fetchone()
                
                if statistiques_produit:
                    production['comparaison'] = statistiques_produit
                
        except Exception as e:
            flash(f'Erreur lors de la récupération des détails de production: {str(e)}', 'danger')
            logger.error(f"Erreur détails production {production_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('production/details.html', 
                          production=production, 
                          controles_qualite=controles_qualite,
                          details_lot=details_lot)

@app.route('/production/<int:production_id>/controle', methods=['GET', 'POST'])
@login_required
@role_required('operator')
@log_activity('controle_qualite_production')
def production_controle(production_id):
    """Ajout d'un contrôle qualité depuis la fiche de production."""
    conn = get_db_connection()
    production = None
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer les informations de la production
                sql = """
                SELECT p.*, pr.nom as produit_nom, pr.reference
                FROM production p
                JOIN produits pr ON p.produit_id = pr.id
                WHERE p.id = %s
                """
                cursor.execute(sql, (production_id,))
                production = cursor.fetchone()
                
                if not production:
                    flash('Production non trouvée', 'warning')
                    return redirect(url_for('production_liste'))
                
                if request.method == 'POST':
                    type_controle = request.form.get('type_controle')
                    resultat = request.form.get('resultat')
                    commentaire = request.form.get('commentaire')
                    mesures = request.form.get('mesures', '{}')
                    
                    # Gérer l'upload d'un rapport si présent
                    rapport_url = None
                    if 'rapport' in request.files:
                        rapport_file = request.files['rapport']
                        if rapport_file and rapport_file.filename != '' and allowed_file(rapport_file.filename):
                            secure_name = sanitize_filename(rapport_file.filename)
                            unique_filename = generate_unique_filename(secure_name)
                            
                            rapport_dir = os.path.join(app.config['UPLOAD_FOLDER'], 'rapports')
                            os.makedirs(rapport_dir, exist_ok=True)
                            
                            filepath = os.path.join(rapport_dir, unique_filename)
                            rapport_file.save(filepath)
                            rapport_url = f"/static/uploads/rapports/{unique_filename}"
                    
                    # Enregistrer le contrôle qualité
                    cursor.execute("""
                        INSERT INTO controles_qualite 
                        (produit_id, lot_id, numero_lot, type_controle, resultat, 
                        commentaire, mesures, rapport_url, utilisateur_id, date_controle)
                        VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                    """, (
                        production['produit_id'], 
                        production_id, 
                        production['numero_lot'], 
                        type_controle, 
                        resultat, 
                        commentaire, 
                        mesures, 
                        rapport_url, 
                        session['user_id'], 
                        datetime.now()
                    ))
                    conn.commit()
                    
                    # Enregistrer dans les logs
                    log_message = f"Contrôle qualité ajouté pour production ID {production_id}: {resultat}"
                    logger.info(log_message)
                    
                    # Notification en cas de non-conformité
                    if resultat == 'non_conforme':
                        # Envoyer une alerte aux superviseurs
                        cursor.execute("""
                            SELECT email FROM utilisateurs 
                            WHERE role IN ('supervisor', 'manager', 'admin') AND actif = 1
                        """)
                        emails = [row['email'] for row in cursor.fetchall()]
                        
                        if emails:
                            sujet = f"Alerte qualité: Non-conformité détectée - {production['produit_nom']}"
                            corps = f"""
                            Une non-conformité a été détectée lors d'un contrôle qualité :
                            
                            Produit: {production['produit_nom']} ({production['reference']})
                            Lot: {production['numero_lot']}
                            Date de production: {production['date_creation']}
                            
                            Commentaire du contrôle: {commentaire}
                            
                            Veuillez prendre les mesures nécessaires.
                            """
                            
                            send_notification_email(sujet, emails, corps)
                    
                    flash(f'Contrôle qualité enregistré avec succès: {resultat}', 'success')
                    return redirect(url_for('production_details', production_id=production_id))
                
        except Exception as e:
            flash(f'Erreur lors de l\'ajout du contrôle qualité: {str(e)}', 'danger')
            logger.error(f"Erreur contrôle qualité production {production_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('production/controle.html', production=production)

@app.route('/production/planning')
@login_required
@log_activity('planning_production')
def production_planning():
    """Affichage du planning de production."""
    conn = get_db_connection()
    plannings = []
    
    # Paramètres de filtrage
    date_debut = request.args.get('date_debut', datetime.now().strftime('%Y-%m-%d'))
    date_fin = request.args.get('date_fin', (datetime.now() + timedelta(days=7)).strftime('%Y-%m-%d'))
    ligne_id = request.args.get('ligne_id', type=int)
    statut = request.args.get('statut')
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Liste des lignes pour le filtre
                cursor.execute("SELECT id, nom FROM lignes_production WHERE actif = 1 ORDER BY nom")
                lignes = cursor.fetchall()
                
                # Construction de la requête
                sql = """
                SELECT pl.*, pr.nom as produit_nom, pr.reference, l.nom as ligne_nom,
                       u.prenom, u.nom as nom_utilisateur
                FROM planning_production pl
                JOIN produits pr ON pl.produit_id = pr.id
                JOIN lignes_production l ON pl.ligne_production_id = l.id
                JOIN utilisateurs u ON pl.utilisateur_id = u.id
                WHERE pl.date_production BETWEEN %s AND %s
                """
                params = [date_debut, date_fin]
                
                if ligne_id:
                    sql += " AND pl.ligne_production_id = %s"
                    params.append(ligne_id)
                
                if statut:
                    sql += " AND pl.statut = %s"
                    params.append(statut)
                
                sql += " ORDER BY pl.date_production, pl.heure_debut"
                
                cursor.execute(sql, params)
                plannings = cursor.fetchall()
                
                # Formater les statuts pour l'affichage
                for p in plannings:
                    if p['statut'] == 'planifie':
                        p['statut_affichage'] = 'Planifié'
                        p['classe_statut'] = 'info'
                    elif p['statut'] == 'en_cours':
                        p['statut_affichage'] = 'En cours'
                        p['classe_statut'] = 'warning'
                    elif p['statut'] == 'termine':
                        p['statut_affichage'] = 'Terminé'
                        p['classe_statut'] = 'success'
                    elif p['statut'] == 'annule':
                        p['statut_affichage'] = 'Annulé'
                        p['classe_statut'] = 'danger'
                    else:
                        p['statut_affichage'] = p['statut'].capitalize()
                        p['classe_statut'] = 'secondary'
                
        except Exception as e:
            flash(f'Erreur lors de la récupération du planning: {str(e)}', 'danger')
            logger.error(f"Erreur planning production: {str(e)}")
        finally:
            conn.close()
    
    return render_template('production/planning.html', 
                          plannings=plannings,
                          lignes=lignes if 'lignes' in locals() else [],
                          filtres={
                              'date_debut': date_debut,
                              'date_fin': date_fin,
                              'ligne_id': ligne_id,
                              'statut': statut
                          })

@app.route('/production/planning/ajouter', methods=['GET', 'POST'])
@login_required
@role_required('supervisor')
@log_activity('ajout_planning_production')
def production_planning_ajouter():
    """Ajout d'un planning de production."""
    conn = get_db_connection()
    produits = []
    lignes = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Liste des produits
                cursor.execute("SELECT id, nom, reference FROM produits WHERE actif = 1 ORDER BY nom")
                produits = cursor.fetchall()
                
                # Liste des lignes de production
                cursor.execute("SELECT id, nom FROM lignes_production WHERE actif = 1 ORDER BY nom")
                lignes = cursor.fetchall()
                
                if request.method == 'POST':
                    produit_id = request.form.get('produit_id')
                    ligne_production_id = request.form.get('ligne_production_id')
                    date_production = request.form.get('date_production')
                    heure_debut = request.form.get('heure_debut')
                    heure_fin = request.form.get('heure_fin')
                    quantite_prevue = request.form.get('quantite_prevue')
                    priorite = request.form.get('priorite', 'normale')
                    commentaire = request.form.get('commentaire')
                    
                    # Validation des données
                    if not all([produit_id, ligne_production_id, date_production, heure_debut, heure_fin, quantite_prevue]):
                        flash('Tous les champs obligatoires doivent être remplis', 'danger')
                        return render_template('production/planning_ajouter.html', produits=produits, lignes=lignes)
                    
                    # Vérifier la disponibilité de la ligne
                    cursor.execute("""
                        SELECT id FROM planning_production
                        WHERE ligne_production_id = %s AND date_production = %s AND statut IN ('planifie', 'en_cours')
                        AND ((heure_debut <= %s AND heure_fin > %s) OR
                             (heure_debut < %s AND heure_fin >= %s) OR
                             (heure_debut >= %s AND heure_fin <= %s))
                    """, (
                        ligne_production_id, date_production, 
                        heure_debut, heure_debut,
                        heure_fin, heure_fin, 
                        heure_debut, heure_fin
                    ))
                    conflit = cursor.fetchone()
                    
                    if conflit:
                        flash('La ligne de production est déjà réservée pour cette période', 'danger')
                        return render_template('production/planning_ajouter.html', produits=produits, lignes=lignes)
                    
                    # Enregistrer le planning
                    cursor.execute("""
                        INSERT INTO planning_production 
                        (produit_id, ligne_production_id, date_production, heure_debut, heure_fin,
                         quantite_prevue, priorite, statut, commentaire, utilisateur_id, date_creation)
                        VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                    """, (
                        produit_id, ligne_production_id, date_production, heure_debut, heure_fin,
                        quantite_prevue, priorite, 'planifie', commentaire, session['user_id'], datetime.now()
                    ))
                    conn.commit()
                    
                    # Récupérer les informations pour le log
                    cursor.execute("SELECT nom, reference FROM produits WHERE id = %s", (produit_id,))
                    produit_info = cursor.fetchone()
                    cursor.execute("SELECT nom FROM lignes_production WHERE id = %s", (ligne_production_id,))
                    ligne_info = cursor.fetchone()
                    
                    log_message = f"Planning ajouté: {produit_info['nom']} ({produit_info['reference']}) sur {ligne_info['nom']} le {date_production} de {heure_debut} à {heure_fin}"
                    flash('Planning de production ajouté avec succès', 'success')
                    logger.info(log_message)
                    
                    return redirect(url_for('production_planning'))
                
        except Exception as e:
            flash(f'Erreur lors de l\'ajout du planning: {str(e)}', 'danger')
            logger.error(f"Erreur ajout planning: {str(e)}")
        finally:
            conn.close()
    
    return render_template('production/planning_ajouter.html', produits=produits, lignes=lignes)

@app.route('/production/planning/<int:planning_id>/modifier', methods=['GET', 'POST'])
@login_required
@role_required('supervisor')
@log_activity('modification_planning_production')
@audit_trail('planning_production')
def production_planning_modifier(planning_id):
    """Modification d'un planning de production."""
    conn = get_db_connection()
    planning = None
    produits = []
    lignes = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer le planning
                sql = """
                SELECT pl.* 
                FROM planning_production pl
                WHERE pl.id = %s
                """
                cursor.execute(sql, (planning_id,))
                planning = cursor.fetchone()
                
                if not planning:
                    flash('Planning non trouvé', 'warning')
                    return redirect(url_for('production_planning'))
                
                # Vérifier si le planning peut être modifié
                if planning['statut'] in ['termine', 'annule']:
                    flash('Ce planning ne peut plus être modifié', 'danger')
                    return redirect(url_for('production_planning'))
                
                # Liste des produits
                cursor.execute("SELECT id, nom, reference FROM produits WHERE actif = 1 ORDER BY nom")
                produits = cursor.fetchall()
                
                # Liste des lignes de production
                cursor.execute("SELECT id, nom FROM lignes_production WHERE actif = 1 ORDER BY nom")
                lignes = cursor.fetchall()
                
                if request.method == 'POST':
                    produit_id = request.form.get('produit_id')
                    ligne_production_id = request.form.get('ligne_production_id')
                    date_production = request.form.get('date_production')
                    heure_debut = request.form.get('heure_debut')
                    heure_fin = request.form.get('heure_fin')
                    quantite_prevue = request.form.get('quantite_prevue')
                    priorite = request.form.get('priorite')
                    statut = request.form.get('statut')
                    commentaire = request.form.get('commentaire')
                    
                    # Validation
                    if not all([produit_id, ligne_production_id, date_production, heure_debut, heure_fin, quantite_prevue, statut]):
                        flash('Tous les champs obligatoires doivent être remplis', 'danger')
                        return render_template('production/planning_modifier.html', planning=planning, produits=produits, lignes=lignes)
                    
                    # Vérifier la disponibilité de la ligne (sauf pour lui-même)
                    if (ligne_production_id != str(planning['ligne_production_id']) or 
                        date_production != planning['date_production'].strftime('%Y-%m-%d') or 
                        heure_debut != planning['heure_debut'].strftime('%H:%M') or 
                        heure_fin != planning['heure_fin'].strftime('%H:%M')):
                        
                        cursor.execute("""
                            SELECT id FROM planning_production
                            WHERE id != %s AND ligne_production_id = %s AND date_production = %s AND statut IN ('planifie', 'en_cours')
                            AND ((heure_debut <= %s AND heure_fin > %s) OR
                                 (heure_debut < %s AND heure_fin >= %s) OR
                                 (heure_debut >= %s AND heure_fin <= %s))
                        """, (
                            planning_id, ligne_production_id, date_production, 
                            heure_debut, heure_debut,
                            heure_fin, heure_fin, 
                            heure_debut, heure_fin
                        ))
                        conflit = cursor.fetchone()
                        
                        if conflit:
                            flash('La ligne de production est déjà réservée pour cette période', 'danger')
                            return render_template('production/planning_modifier.html', planning=planning, produits=produits, lignes=lignes)
                    
                    # Mise à jour du planning
                    cursor.execute("""
                        UPDATE planning_production 
                        SET produit_id = %s, ligne_production_id = %s, date_production = %s, 
                            heure_debut = %s, heure_fin = %s, quantite_prevue = %s, 
                            priorite = %s, statut = %s, commentaire = %s, date_modification = %s
                        WHERE id = %s
                    """, (
                        produit_id, ligne_production_id, date_production, heure_debut, heure_fin,
                        quantite_prevue, priorite, statut, commentaire, datetime.now(), planning_id
                    ))
                    conn.commit()
                    
                    # Si le planning est passé à 'termine', créer automatiquement une production
                    if statut == 'termine' and planning['statut'] != 'termine':
                        # Créer l'enregistrement de production
                        temps_production = (datetime.strptime(heure_fin, '%H:%M') - datetime.strptime(heure_debut, '%H:%M')).seconds / 3600
                        
                        cursor.execute("""
                            INSERT INTO production 
                            (produit_id, ligne_production_id, quantite_produite, temps_production, 
                             commentaire, planning_id, utilisateur_id, date_creation)
                            VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                        """, (
                            produit_id, ligne_production_id, quantite_prevue, temps_production, 
                            f"Production automatique depuis planning ID {planning_id}", 
                            planning_id, session['user_id'], datetime.now()
                        ))
                        
                        production_id = cursor.lastrowid
                        
                        # Mettre à jour le stock
                        cursor.execute("""
                            SELECT id FROM entrepots WHERE est_production = 1 AND actif = 1 LIMIT 1
                        """)
                        entrepot_production = cursor.fetchone()
                        
                        if entrepot_production:
                            entrepot_id = entrepot_production['id']
                            
                            # Vérifier si le stock existe
                            cursor.execute("""
                                SELECT id FROM stocks 
                                WHERE produit_id = %s AND entrepot_id = %s AND actif = 1
                            """, (produit_id, entrepot_id))
                            stock = cursor.fetchone()
                            
                            if not stock:
                                # Créer le stock
                                cursor.execute("""
                                    INSERT INTO stocks (produit_id, entrepot_id, quantite, seuil_alerte,
                                                      utilisateur_id, date_creation)
                                    VALUES (%s, %s, 0, 10, %s, %s)
                                """, (produit_id, entrepot_id, session['user_id'], datetime.now()))
                                
                                cursor.execute("""
                                    SELECT id FROM stocks 
                                    WHERE produit_id = %s AND entrepot_id = %s AND actif = 1
                                """, (produit_id, entrepot_id))
                                stock = cursor.fetchone()
                            
                            # Ajouter au stock
                            cursor.execute("""
                                UPDATE stocks 
                                SET quantite = quantite + %s, date_modification = %s
                                WHERE id = %s
                            """, (quantite_prevue, datetime.now(), stock['id']))
                            
                            # Enregistrer le mouvement de stock
                            cursor.execute("""
                                INSERT INTO mouvements_stock 
                                (produit_id, entrepot_id, type_mouvement, quantite, commentaire,
                                utilisateur_id, date_mouvement, production_id)
                                VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                            """, (
                                produit_id, entrepot_id, 'production', quantite_prevue, 
                                f"Production auto depuis planning ID {planning_id}", 
                                session['user_id'], datetime.now(), production_id
                            ))
                            
                            conn.commit()
                            flash('Production automatiquement créée et stock mis à jour', 'info')
                    
                    flash('Planning de production modifié avec succès', 'success')
                    logger.info(f"Planning modifié: ID {planning_id}")
                    return redirect(url_for('production_planning'))
                
        except Exception as e:
            flash(f'Erreur lors de la modification du planning: {str(e)}', 'danger')
            logger.error(f"Erreur modification planning {planning_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('production/planning_modifier.html', planning=planning, produits=produits, lignes=lignes)

@app.route('/production/planning/<int:planning_id>/supprimer', methods=['POST'])
@login_required
@role_required('manager')
@log_activity('suppression_planning_production')
def production_planning_supprimer(planning_id):
    """Annulation d'un planning de production."""
    conn = get_db_connection()
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Vérifier si le planning existe
                cursor.execute("SELECT * FROM planning_production WHERE id = %s", (planning_id,))
                planning = cursor.fetchone()
                
                if not planning:
                    flash('Planning non trouvé', 'warning')
                    return redirect(url_for('production_planning'))
                
                # Vérifier si le planning peut être annulé
                if planning['statut'] == 'termine':
                    flash('Un planning terminé ne peut pas être annulé', 'danger')
                    return redirect(url_for('production_planning'))
                
                # Annuler le planning
                cursor.execute("""
                    UPDATE planning_production 
                    SET statut = 'annule', date_modification = %s, commentaire = CONCAT(commentaire, ' | Annulé le ', %s)
                    WHERE id = %s
                """, (datetime.now(), datetime.now().strftime('%Y-%m-%d %H:%M'), planning_id))
                conn.commit()
                
                flash('Planning de production annulé avec succès', 'success')
                logger.info(f"Planning annulé: ID {planning_id}")
                return redirect(url_for('production_planning'))
                
        except Exception as e:
            flash(f'Erreur lors de l\'annulation du planning: {str(e)}', 'danger')
            logger.error(f"Erreur annulation planning {planning_id}: {str(e)}")
        finally:
            conn.close()
    
    return redirect(url_for('production_planning'))

@app.route('/production/lignes')
@login_required
@log_activity('liste_lignes_production')
def production_lignes():
    """Liste des lignes de production."""
    conn = get_db_connection()
    lignes = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer les lignes de production
                sql = """
                SELECT l.*, u.prenom, u.nom as nom_utilisateur 
                FROM lignes_production l
                LEFT JOIN utilisateurs u ON l.utilisateur_id = u.id
                WHERE l.actif = 1
                ORDER BY l.nom
                """
                cursor.execute(sql)
                lignes = cursor.fetchall()
                
                # Récupérer le statut actuel des lignes
                for ligne in lignes:
                    # Vérifier s'il y a une production en cours
                    cursor.execute("""
                        SELECT pl.*, p.nom as produit_nom, p.reference 
                        FROM planning_production pl
                        JOIN produits p ON pl.produit_id = p.id
                        WHERE pl.ligne_production_id = %s 
                        AND pl.statut = 'en_cours'
                        LIMIT 1
                    """, (ligne['id'],))
                    production_en_cours = cursor.fetchone()
                    
                    if production_en_cours:
                        ligne['status'] = 'occupee'
                        ligne['production_en_cours'] = production_en_cours
                    else:
                        # Vérifier le dernier status de maintenance
                        cursor.execute("""
                            SELECT m.statut 
                            FROM maintenance m
                            JOIN equipements e ON m.equipement_id = e.id
                            WHERE e.ligne_production_id = %s 
                            ORDER BY m.date_programmee DESC
                            LIMIT 1
                        """, (ligne['id'],))
                        derniere_maintenance = cursor.fetchone()
                        
                        if derniere_maintenance and derniere_maintenance['statut'] == 'en_cours':
                            ligne['status'] = 'maintenance'
                        else:
                            ligne['status'] = 'disponible'
                    
                    # Récupérer les statistiques de production
                    cursor.execute("""
                        SELECT COUNT(*) as nb_productions,
                               SUM(quantite_produite) as total_produit,
                               AVG(temps_production) as temps_moyen
                        FROM production
                        WHERE ligne_production_id = %s
                        AND date_creation >= DATE_SUB(NOW(), INTERVAL 30 DAY)
                    """, (ligne['id'],))
                    stats = cursor.fetchone()
                    ligne['stats'] = stats
                    
                    # Récupérer les équipements associés
                    cursor.execute("""
                        SELECT id, nom, statut FROM equipements 
                        WHERE ligne_production_id = %s AND actif = 1
                    """, (ligne['id'],))
                    ligne['equipements'] = cursor.fetchall()
        except Exception as e:
            flash(f'Erreur lors de la récupération des lignes de production: {str(e)}', 'danger')
            logger.error(f"Erreur liste lignes: {str(e)}")
        finally:
            conn.close()
    
    return render_template('production/lignes.html', lignes=lignes)

@app.route('/production/lignes/<int:ligne_id>')
@login_required
@log_activity('details_ligne_production')
def production_ligne_details(ligne_id):
    """Détails d'une ligne de production."""
    conn = get_db_connection()
    ligne = None
    productions = []
    plannings = []
    equipements = []
    maintenances = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer les détails de la ligne
                sql = """
                SELECT l.*, u.prenom, u.nom as nom_utilisateur
                FROM lignes_production l
                LEFT JOIN utilisateurs u ON l.utilisateur_id = u.id
                WHERE l.id = %s
                """
                cursor.execute(sql, (ligne_id,))
                ligne = cursor.fetchone()
                
                if not ligne:
                    flash('Ligne de production non trouvée', 'warning')
                    return redirect(url_for('production_lignes'))
                
                # Récupérer les dernières productions
                sql = """
                SELECT p.*, pr.nom as produit_nom, pr.reference,
                       u.prenom, u.nom as nom_utilisateur
                FROM production p
                JOIN produits pr ON p.produit_id = pr.id
                JOIN utilisateurs u ON p.utilisateur_id = u.id
                WHERE p.ligne_production_id = %s
                ORDER BY p.date_creation DESC
                LIMIT 10
                """
                cursor.execute(sql, (ligne_id,))
                productions = cursor.fetchall()
                
                # Récupérer les plannings à venir
                sql = """
                SELECT pl.*, pr.nom as produit_nom, pr.reference,
                       u.prenom, u.nom as nom_utilisateur
                FROM planning_production pl
                JOIN produits pr ON pl.produit_id = pr.id
                JOIN utilisateurs u ON pl.utilisateur_id = u.id
                WHERE pl.ligne_production_id = %s AND pl.date_production >= CURDATE() AND pl.statut IN ('planifie', 'en_cours')
                ORDER BY pl.date_production, pl.heure_debut
                LIMIT 10
                """
                cursor.execute(sql, (ligne_id,))
                plannings = cursor.fetchall()
                
                # Récupérer les équipements associés
                sql = """
                SELECT e.*, u.prenom, u.nom as nom_utilisateur
                FROM equipements e
                LEFT JOIN utilisateurs u ON e.utilisateur_id = u.id
                WHERE e.ligne_production_id = %s AND e.actif = 1
                ORDER BY e.nom
                """
                cursor.execute(sql, (ligne_id,))
                equipements = cursor.fetchall()
                
                # Récupérer les maintenances associées
                sql = """
                SELECT m.*, e.nom as equipement_nom, t.nom as type_nom,
                       u.prenom, u.nom as nom_utilisateur
                FROM maintenance m
                JOIN equipements e ON m.equipement_id = e.id
                JOIN types_maintenance t ON m.type_maintenance_id = t.id
                JOIN utilisateurs u ON m.utilisateur_id = u.id
                WHERE e.ligne_production_id = %s
                ORDER BY m.date_programmee DESC
                LIMIT 10
                """
                cursor.execute(sql, (ligne_id,))
                maintenances = cursor.fetchall()
                
                # Calculer les statistiques de production
                cursor.execute("""
                    SELECT SUM(quantite_produite) as total_produit,
                           AVG(quantite_produite) as moyenne_produit,
                           AVG(temps_production) as temps_moyen,
                           MAX(date_creation) as derniere_production
                    FROM production
                    WHERE ligne_production_id = %s
                """, (ligne_id,))
                stats_global = cursor.fetchone()
                
                # Statistiques par mois (6 derniers mois)
                cursor.execute("""
                    SELECT DATE_FORMAT(date_creation, '%Y-%m') as mois,
                           SUM(quantite_produite) as total,
                           COUNT(*) as nb_productions,
                           AVG(temps_production) as temps_moyen
                    FROM production
                    WHERE ligne_production_id = %s
                    AND date_creation >= DATE_SUB(NOW(), INTERVAL 6 MONTH)
                    GROUP BY mois
                    ORDER BY mois
                """, (ligne_id,))
                stats_mensuel = cursor.fetchall()
                
                # Créer un graphique de production mensuelle
                if stats_mensuel:
                    plt.figure(figsize=(10, 6))
                    
                    mois = [m['mois'] for m in stats_mensuel]
                    productions = [m['total'] for m in stats_mensuel]
                    
                    plt.bar(mois, productions)
                    plt.title(f'Production mensuelle - {ligne["nom"]}')
                    plt.xlabel('Mois')
                    plt.ylabel('Quantité produite')
                    plt.grid(True, linestyle='--', alpha=0.7)
                    plt.xticks(rotation=45)
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    ligne['graphique'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
        except Exception as e:
            flash(f'Erreur lors de la récupération des détails de la ligne: {str(e)}', 'danger')
            logger.error(f"Erreur détails ligne {ligne_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('production/ligne_details.html', 
                          ligne=ligne, 
                          productions=productions,
                          plannings=plannings,
                          equipements=equipements,
                          maintenances=maintenances,
                          stats_global=stats_global if 'stats_global' in locals() else None,
                          stats_mensuel=stats_mensuel if 'stats_mensuel' in locals() else None)

# =============================================================================
# GESTION DE LA MAINTENANCE
# =============================================================================

@app.route('/maintenance')
@login_required
@log_activity('liste_maintenance')
def maintenance_liste():
    """Liste des maintenances planifiées et historique."""
    conn = get_db_connection()
    maintenances = []
    
    # Paramètres de filtrage
    statut = request.args.get('statut')
    equipement_id = request.args.get('equipement_id', type=int)
    type_maintenance_id = request.args.get('type_maintenance_id', type=int)
    priorite = request.args.get('priorite')
    date_debut = request.args.get('date_debut')
    date_fin = request.args.get('date_fin')
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer les listes pour les filtres
                cursor.execute("SELECT id, nom FROM equipements WHERE actif = 1 ORDER BY nom")
                equipements = cursor.fetchall()
                
                cursor.execute("SELECT id, nom FROM types_maintenance ORDER BY nom")
                types_maintenance = cursor.fetchall()
                
                # Construction de la requête
                sql = """
                SELECT m.*, e.nom as equipement_nom, e.ligne_production_id, 
                       l.nom as ligne_nom, t.nom as type_nom,
                       u.prenom, u.nom as nom_utilisateur
                FROM maintenance m
                JOIN equipements e ON m.equipement_id = e.id
                LEFT JOIN lignes_production l ON e.ligne_production_id = l.id
                JOIN types_maintenance t ON m.type_maintenance_id = t.id
                JOIN utilisateurs u ON m.utilisateur_id = u.id
                WHERE 1=1
                """
                params = []
                
                # Ajouter les filtres
                if statut:
                    sql += " AND m.statut = %s"
                    params.append(statut)
                
                if equipement_id:
                    sql += " AND m.equipement_id = %s"
                    params.append(equipement_id)
                
                if type_maintenance_id:
                    sql += " AND m.type_maintenance_id = %s"
                    params.append(type_maintenance_id)
                
                if priorite:
                    sql += " AND m.priorite = %s"
                    params.append(priorite)
                
                if date_debut:
                    sql += " AND m.date_programmee >= %s"
                    params.append(date_debut)
                
                if date_fin:
                    sql += " AND m.date_programmee <= %s"
                    params.append(date_fin)
                
                # Tri par défaut: priorité décroissante et date
                sql += """ 
                ORDER BY 
                    CASE 
                        WHEN m.statut = 'en_cours' THEN 1
                        WHEN m.statut = 'planifie' THEN 2
                        ELSE 3
                    END,
                    CASE 
                        WHEN m.priorite = 'haute' THEN 1
                        WHEN m.priorite = 'moyenne' THEN 2
                        ELSE 3
                    END,
                    m.date_programmee
                """
                
                cursor.execute(sql, params)
                maintenances = cursor.fetchall()
                
                # Formater les statuts pour l'affichage
                for m in maintenances:
                    if m['statut'] == 'en_cours':
                        m['statut_affichage'] = 'En cours'
                        m['classe_statut'] = 'warning'
                    elif m['statut'] == 'planifie':
                        m['statut_affichage'] = 'Planifiée'
                        m['classe_statut'] = 'info'
                    elif m['statut'] == 'terminee':
                        m['statut_affichage'] = 'Terminée'
                        m['classe_statut'] = 'success'
                    else:
                        m['statut_affichage'] = 'Annulée'
                        m['classe_statut'] = 'danger'
                    
                    # Classe pour la priorité
                    if m['priorite'] == 'haute':
                        m['classe_priorite'] = 'danger'
                    elif m['priorite'] == 'moyenne':
                        m['classe_priorite'] = 'warning'
                    else:
                        m['classe_priorite'] = 'info'
                
                # Récupérer les statistiques
                cursor.execute("""
                    SELECT 
                        COUNT(*) as total,
                        SUM(CASE WHEN statut = 'planifie' THEN 1 ELSE 0 END) as planifiees,
                        SUM(CASE WHEN statut = 'en_cours' THEN 1 ELSE 0 END) as en_cours,
                        SUM(CASE WHEN statut = 'terminee' THEN 1 ELSE 0 END) as terminees,
                        SUM(CASE WHEN priorite = 'haute' THEN 1 ELSE 0 END) as priorite_haute
                    FROM maintenance
                    WHERE date_programmee BETWEEN DATE_SUB(NOW(), INTERVAL 30 DAY) AND DATE_ADD(NOW(), INTERVAL 30 DAY)
                """)
                statistiques = cursor.fetchone()
                
        except Exception as e:
            flash(f'Erreur lors de la récupération des maintenances: {str(e)}', 'danger')
            logger.error(f"Erreur liste maintenance: {str(e)}")
        finally:
            conn.close()
    
    return render_template('maintenance/liste.html', 
                          maintenances=maintenances,
                          equipements=equipements if 'equipements' in locals() else [],
                          types_maintenance=types_maintenance if 'types_maintenance' in locals() else [],
                          statistiques=statistiques if 'statistiques' in locals() else None,
                          priorites=[
                              {'code': 'haute', 'nom': 'Haute'},
                              {'code': 'moyenne', 'nom': 'Moyenne'},
                              {'code': 'basse', 'nom': 'Basse'}
                          ],
                          statuts=[
                              {'code': 'planifie', 'nom': 'Planifiée'},
                              {'code': 'en_cours', 'nom': 'En cours'},
                              {'code': 'terminee', 'nom': 'Terminée'},
                              {'code': 'annulee', 'nom': 'Annulée'}
                          ],
                          filtres={
                              'statut': statut,
                              'equipement_id': equipement_id,
                              'type_maintenance_id': type_maintenance_id,
                              'priorite': priorite,
                              'date_debut': date_debut,
                              'date_fin': date_fin
                          })

@app.route('/maintenance/ajouter', methods=['GET', 'POST'])
@login_required
@role_required('operator')
@log_activity('ajout_maintenance')
def maintenance_ajouter():
    """Ajout d'une maintenance planifiée."""
    conn = get_db_connection()
    equipements = []
    types_maintenance = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Liste des équipements
                cursor.execute("""
                    SELECT e.id, e.nom, l.nom as ligne_nom 
                    FROM equipements e
                    LEFT JOIN lignes_production l ON e.ligne_production_id = l.id
                    WHERE e.actif = 1
                    ORDER BY e.nom
                """)
                equipements = cursor.fetchall()
                
                # Liste des types de maintenance
                cursor.execute("SELECT id, nom, description FROM types_maintenance ORDER BY nom")
                types_maintenance = cursor.fetchall()
                
                if request.method == 'POST':
                    equipement_id = request.form.get('equipement_id')
                    type_maintenance_id = request.form.get('type_maintenance_id')
                    date_programmee = request.form.get('date_programmee')
                    duree_estimee = request.form.get('duree_estimee')
                    description = request.form.get('description')
                    statut = request.form.get('statut', 'planifie')
                    priorite = request.form.get('priorite', 'moyenne')
                    impact_production = request.form.get('impact_production', 'non')
                    
                    # Validation
                    if not all([equipement_id, type_maintenance_id, date_programmee, duree_estimee]):
                        flash('Tous les champs obligatoires doivent être remplis', 'danger')
                        return render_template('maintenance/ajouter.html', equipements=equipements, types_maintenance=types_maintenance)
                    
                    # Vérifier les conflits de maintenance
                    cursor.execute("""
                        SELECT COUNT(*) as nb FROM maintenance 
                        WHERE equipement_id = %s 
                        AND statut IN ('planifie', 'en_cours')
                        AND date_programmee = %s
                    """, (equipement_id, date_programmee))
                    conflit = cursor.fetchone()['nb'] > 0
                    
                    if conflit:
                        flash('Une maintenance est déjà planifiée pour cet équipement à cette date', 'warning')
                    
                    # Enregistrer la maintenance
                    cursor.execute("""
                        INSERT INTO maintenance 
                        (equipement_id, type_maintenance_id, date_programmee, duree_estimee,
                         description, statut, priorite, impact_production, utilisateur_id, date_creation)
                        VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                    """, (
                        equipement_id, type_maintenance_id, date_programmee, duree_estimee,
                        description, statut, priorite, impact_production, session['user_id'], datetime.now()
                    ))
                    maintenance_id = cursor.lastrowid
                    conn.commit()
                    
                    # Récupérer les informations pour le log
                    cursor.execute("SELECT nom FROM equipements WHERE id = %s", (equipement_id,))
                    equipement_info = cursor.fetchone()
                    cursor.execute("SELECT nom FROM types_maintenance WHERE id = %s", (type_maintenance_id,))
                    type_info = cursor.fetchone()
                    
                    log_message = f"Maintenance ajoutée: {type_info['nom']} pour {equipement_info['nom']} le {date_programmee}"
                    flash('Maintenance ajoutée avec succès', 'success')
                    logger.info(log_message)
                    
                    # Si impact sur la production, notifier les superviseurs
                    if impact_production == 'oui':
                        cursor.execute("""
                            SELECT e.nom as equipement_nom, l.nom as ligne_nom
                            FROM equipements e
                            LEFT JOIN lignes_production l ON e.ligne_production_id = l.id
                            WHERE e.id = %s
                        """, (equipement_id,))
                        info = cursor.fetchone()
                        
                        if info and info['ligne_nom']:
                            # Récupérer les emails des superviseurs
                            cursor.execute("""
                                SELECT email FROM utilisateurs 
                                WHERE role IN ('supervisor', 'manager', 'admin') AND actif = 1
                            """)
                            emails = [row['email'] for row in cursor.fetchall()]
                            
                            if emails:
                                sujet = f"Impact production: Maintenance planifiée pour {info['equipement_nom']}"
                                corps = f"""
                                Une maintenance avec impact sur la production a été planifiée:
                                
                                Équipement: {info['equipement_nom']}
                                Ligne de production: {info['ligne_nom']}
                                Type: {type_info['nom']}
                                Date: {date_programmee}
                                Durée estimée: {duree_estimee} heures
                                Priorité: {priorite}
                                
                                Description: {description}
                                
                                Veuillez planifier la production en conséquence.
                                """
                                
                                send_notification_email(sujet, emails, corps)
                    
                    return redirect(url_for('maintenance_liste'))
                
        except Exception as e:
            flash(f'Erreur lors de l\'ajout de la maintenance: {str(e)}', 'danger')
            logger.error(f"Erreur ajout maintenance: {str(e)}")
        finally:
            conn.close()
    
    return render_template('maintenance/ajouter.html', equipements=equipements, types_maintenance=types_maintenance)

@app.route('/maintenance/<int:maintenance_id>', methods=['GET', 'POST'])
@login_required
@log_activity('details_maintenance')
def maintenance_details(maintenance_id):
    """Détails d'une maintenance et ajout d'interventions."""
    conn = get_db_connection()
    maintenance = None
    historique = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Détails de la maintenance
                sql = """
                SELECT m.*, e.nom as equipement_nom, e.numero_serie, e.fabricant, e.modele,
                       l.id as ligne_id, l.nom as ligne_nom,
                       t.nom as type_nom, t.description as type_description,
                       u.prenom, u.nom as nom_utilisateur
                FROM maintenance m
                JOIN equipements e ON m.equipement_id = e.id
                LEFT JOIN lignes_production l ON e.ligne_production_id = l.id
                JOIN types_maintenance t ON m.type_maintenance_id = t.id
                JOIN utilisateurs u ON m.utilisateur_id = u.id
                WHERE m.id = %s
                """
                cursor.execute(sql, (maintenance_id,))
                maintenance = cursor.fetchone()
                
                if not maintenance:
                    flash('Maintenance non trouvée', 'warning')
                    return redirect(url_for('maintenance_liste'))
                
                # Formater le statut pour l'affichage
                if maintenance['statut'] == 'en_cours':
                    maintenance['statut_affichage'] = 'En cours'
                    maintenance['classe_statut'] = 'warning'
                elif maintenance['statut'] == 'planifie':
                    maintenance['statut_affichage'] = 'Planifiée'
                    maintenance['classe_statut'] = 'info'
                elif maintenance['statut'] == 'terminee':
                    maintenance['statut_affichage'] = 'Terminée'
                    maintenance['classe_statut'] = 'success'
                else:
                    maintenance['statut_affichage'] = 'Annulée'
                    maintenance['classe_statut'] = 'danger'
                
                # Historique des interventions
                sql = """
                SELECT i.*, u.prenom, u.nom as nom_utilisateur
                FROM interventions i
                JOIN utilisateurs u ON i.utilisateur_id = u.id
                WHERE i.maintenance_id = %s
                ORDER BY i.date_intervention DESC
                """
                cursor.execute(sql, (maintenance_id,))
                historique = cursor.fetchall()
                
                # Traitement du formulaire d'ajout d'intervention
                if request.method == 'POST':
                    # Vérifier si la maintenance peut être modifiée
                    if maintenance['statut'] == 'annulee':
                        flash('Impossible d\'ajouter une intervention à une maintenance annulée', 'danger')
                        return redirect(url_for('maintenance_details', maintenance_id=maintenance_id))
                    elif maintenance['statut'] == 'terminee' and not has_permission('supervisor'):
                        flash('Seuls les superviseurs peuvent ajouter des interventions à une maintenance terminée', 'danger')
                        return redirect(url_for('maintenance_details', maintenance_id=maintenance_id))
                    
                    date_intervention = request.form.get('date_intervention')
                    duree_reelle = request.form.get('duree_reelle')
                    description = request.form.get('description')
                    statut = request.form.get('statut')
                    pieces_remplacees = request.form.get('pieces_remplacees', '')
                    
                    # Gérer le téléchargement d'un rapport si présent
                    rapport_url = None
                    if 'rapport' in request.files:
                        rapport_file = request.files['rapport']
                        if rapport_file and rapport_file.filename != '' and allowed_file(rapport_file.filename):
                            secure_name = sanitize_filename(rapport_file.filename)
                            unique_filename = generate_unique_filename(secure_name)
                            
                            rapport_dir = os.path.join(app.config['UPLOAD_FOLDER'], 'maintenance')
                            os.makedirs(rapport_dir, exist_ok=True)
                            
                            filepath = os.path.join(rapport_dir, unique_filename)
                            rapport_file.save(filepath)
                            rapport_url = f"/static/uploads/maintenance/{unique_filename}"
                    
                    # Enregistrer l'intervention
                    cursor.execute("""
                        INSERT INTO interventions 
                        (maintenance_id, date_intervention, duree_reelle, description, 
                        pieces_remplacees, rapport_url, utilisateur_id, date_creation)
                        VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                    """, (
                        maintenance_id, date_intervention, duree_reelle, description, 
                        pieces_remplacees, rapport_url, session['user_id'], datetime.now()
                    ))
                    
                    # Mettre à jour le statut de la maintenance
                    cursor.execute("""
                        UPDATE maintenance 
                        SET statut = %s, date_modification = %s
                        WHERE id = %s
                    """, (statut, datetime.now(), maintenance_id))
                    
                    # Si terminée, mettre à jour la date de fin
                    if statut == 'terminee':
                        cursor.execute("""
                            UPDATE maintenance 
                            SET date_fin = %s
                            WHERE id = %s AND date_fin IS NULL
                        """, (datetime.now(), maintenance_id))
                    
                    conn.commit()
                    
                    flash('Intervention ajoutée avec succès', 'success')
                    logger.info(f"Intervention ajoutée pour maintenance ID {maintenance_id}")
                    
                    # Si l'équipement est lié à une ligne de production et maintenance terminée
                    if statut == 'terminee' and maintenance['ligne_id']:
                        # Récupérer les emails des superviseurs de production
                        cursor.execute("""
                            SELECT email FROM utilisateurs 
                            WHERE role IN ('supervisor', 'manager') AND actif = 1
                        """)
                        emails = [row['email'] for row in cursor.fetchall()]
                        
                        if emails:
                            sujet = f"Maintenance terminée: {maintenance['equipement_nom']}"
                            corps = f"""
                            La maintenance suivante a été terminée:
                            
                            Équipement: {maintenance['equipement_nom']}
                            Ligne de production: {maintenance['ligne_nom']}
                            Type: {maintenance['type_nom']}
                            
                            Date d'intervention: {date_intervention}
                            Durée: {duree_reelle} heures
                            
                            Description: {description}
                            
                            La ligne de production est à nouveau disponible.
                            """
                            
                            send_notification_email(sujet, emails, corps)
                    
                    return redirect(url_for('maintenance_details', maintenance_id=maintenance_id))
                
        except Exception as e:
            flash(f'Erreur lors de la récupération des détails de maintenance: {str(e)}', 'danger')
            logger.error(f"Erreur détails maintenance {maintenance_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('maintenance/details.html', maintenance=maintenance, historique=historique)

@app.route('/maintenance/<int:maintenance_id>/modifier', methods=['GET', 'POST'])
@login_required
@role_required('supervisor')
@log_activity('modification_maintenance')
@audit_trail('maintenance')
def maintenance_modifier(maintenance_id):
    """Modification d'une maintenance."""
    conn = get_db_connection()
    maintenance = None
    equipements = []
    types_maintenance = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer la maintenance
                cursor.execute("SELECT * FROM maintenance WHERE id = %s", (maintenance_id,))
                maintenance = cursor.fetchone()
                
                if not maintenance:
                    flash('Maintenance non trouvée', 'warning')
                    return redirect(url_for('maintenance_liste'))
                
                # Vérifier si la maintenance peut être modifiée
                if maintenance['statut'] == 'terminee' and not has_permission('manager'):
                    flash('Seuls les managers peuvent modifier une maintenance terminée', 'danger')
                    return redirect(url_for('maintenance_details', maintenance_id=maintenance_id))
                
                # Liste des équipements
                cursor.execute("""
                    SELECT e.id, e.nom, l.nom as ligne_nom 
                    FROM equipements e
                    LEFT JOIN lignes_production l ON e.ligne_production_id = l.id
                    WHERE e.actif = 1
                    ORDER BY e.nom
                """)
                equipements = cursor.fetchall()
                
                # Liste des types de maintenance
                cursor.execute("SELECT id, nom FROM types_maintenance ORDER BY nom")
                types_maintenance = cursor.fetchall()
                
                if request.method == 'POST':
                    equipement_id = request.form.get('equipement_id')
                    type_maintenance_id = request.form.get('type_maintenance_id')
                    date_programmee = request.form.get('date_programmee')
                    duree_estimee = request.form.get('duree_estimee')
                    description = request.form.get('description')
                    statut = request.form.get('statut')
                    priorite = request.form.get('priorite')
                    impact_production = request.form.get('impact_production')
                    
                    # Validation
                    if not all([equipement_id, type_maintenance_id, date_programmee, duree_estimee, statut, priorite]):
                        flash('Tous les champs obligatoires doivent être remplis', 'danger')
                        return render_template('maintenance/modifier.html', 
                                              maintenance=maintenance, 
                                              equipements=equipements, 
                                              types_maintenance=types_maintenance)
                    
                    # Mise à jour de la maintenance
                    cursor.execute("""
                        UPDATE maintenance 
                        SET equipement_id = %s, type_maintenance_id = %s, date_programmee = %s,
                            duree_estimee = %s, description = %s, statut = %s, priorite = %s,
                            impact_production = %s, date_modification = %s
                        WHERE id = %s
                    """, (
                        equipement_id, type_maintenance_id, date_programmee,
                        duree_estimee, description, statut, priorite,
                        impact_production, datetime.now(), maintenance_id
                    ))
                    
                    # Si terminée, mettre à jour la date de fin
                    if statut == 'terminee' and maintenance['statut'] != 'terminee':
                        cursor.execute("""
                            UPDATE maintenance 
                            SET date_fin = %s
                            WHERE id = %s
                        """, (datetime.now(), maintenance_id))
                    
                    conn.commit()
                    
                    flash('Maintenance modifiée avec succès', 'success')
                    logger.info(f"Maintenance modifiée: ID {maintenance_id}")
                    return redirect(url_for('maintenance_details', maintenance_id=maintenance_id))
                
        except Exception as e:
            flash(f'Erreur lors de la modification de la maintenance: {str(e)}', 'danger')
            logger.error(f"Erreur modification maintenance {maintenance_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('maintenance/modifier.html', 
                          maintenance=maintenance, 
                          equipements=equipements, 
                          types_maintenance=types_maintenance)

@app.route('/maintenance/<int:maintenance_id>/annuler', methods=['POST'])
@login_required
@role_required('supervisor')
@log_activity('annulation_maintenance')
def maintenance_annuler(maintenance_id):
    """Annulation d'une maintenance planifiée."""
    conn = get_db_connection()
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Vérifier si la maintenance existe
                cursor.execute("SELECT statut FROM maintenance WHERE id = %s", (maintenance_id,))
                maintenance = cursor.fetchone()
                
                if not maintenance:
                    flash('Maintenance non trouvée', 'warning')
                    return redirect(url_for('maintenance_liste'))
                
                # Vérifier si la maintenance peut être annulée
                if maintenance['statut'] == 'terminee':
                    flash('Une maintenance terminée ne peut pas être annulée', 'danger')
                    return redirect(url_for('maintenance_details', maintenance_id=maintenance_id))
                
                # Récupérer le motif d'annulation
                motif = request.form.get('motif', 'Annulation manuelle')
                
                # Annuler la maintenance
                cursor.execute("""
                    UPDATE maintenance 
                    SET statut = 'annulee', date_modification = %s, 
                        commentaire = CONCAT(COALESCE(commentaire, ''), ' | Motif d\'annulation: ', %s)
                    WHERE id = %s
                """, (datetime.now(), motif, maintenance_id))
                conn.commit()
                
                flash('Maintenance annulée avec succès', 'success')
                logger.info(f"Maintenance annulée: ID {maintenance_id} - Motif: {motif}")
                return redirect(url_for('maintenance_liste'))
                
        except Exception as e:
            flash(f'Erreur lors de l\'annulation de la maintenance: {str(e)}', 'danger')
            logger.error(f"Erreur annulation maintenance {maintenance_id}: {str(e)}")
        finally:
            conn.close()
    
    return redirect(url_for('maintenance_details', maintenance_id=maintenance_id))

@app.route('/maintenance/equipements')
@login_required
@log_activity('liste_equipements')
def maintenance_equipements():
    """Liste des équipements pour la maintenance."""
    conn = get_db_connection()
    equipements = []
    
    # Filtrage
    ligne_id = request.args.get('ligne_id', type=int)
    statut = request.args.get('statut')
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer les lignes pour le filtre
                cursor.execute("SELECT id, nom FROM lignes_production WHERE actif = 1 ORDER BY nom")
                lignes = cursor.fetchall()
                
                # Construction de la requête
                sql = """
                SELECT e.*, l.nom as ligne_nom, u.prenom, u.nom as nom_utilisateur,
                       (SELECT COUNT(*) FROM maintenance m WHERE m.equipement_id = e.id AND m.statut = 'planifie') as nb_maintenance_planifiee,
                       (SELECT COUNT(*) FROM maintenance m WHERE m.equipement_id = e.id AND m.statut = 'en_cours') as nb_maintenance_en_cours,
                       (SELECT MAX(date_fin) FROM maintenance m WHERE m.equipement_id = e.id AND m.statut = 'terminee') as derniere_maintenance
                FROM equipements e
                LEFT JOIN lignes_production l ON e.ligne_production_id = l.id
                LEFT JOIN utilisateurs u ON e.utilisateur_id = u.id
                WHERE e.actif = 1
                """
                params = []
                
                if ligne_id:
                    sql += " AND e.ligne_production_id = %s"
                    params.append(ligne_id)
                
                if statut:
                    sql += " AND e.statut = %s"
                    params.append(statut)
                
                sql += " ORDER BY e.nom"
                
                cursor.execute(sql, params)
                equipements = cursor.fetchall()
                
                # Récupérer les informations supplémentaires pour chaque équipement
                for equipement in equipements:
                    # Dernière intervention
                    cursor.execute("""
                        SELECT m.id, m.statut, m.date_programmee, m.date_fin, t.nom as type_nom 
                        FROM maintenance m
                        JOIN types_maintenance t ON m.type_maintenance_id = t.id
                        WHERE m.equipement_id = %s
                        ORDER BY 
                            CASE WHEN m.statut = 'en_cours' THEN 1
                                 WHEN m.statut = 'planifie' THEN 2
                                 ELSE 3
                            END,
                            m.date_programmee DESC
                        LIMIT 1
                    """, (equipement['id'],))
                    derniere_maintenance = cursor.fetchone()
                    equipement['derniere_maintenance'] = derniere_maintenance
                    
                    # Statut pour affichage
                    if equipement['statut'] == 'operationnel':
                        equipement['statut_affichage'] = 'Opérationnel'
                        equipement['classe_statut'] = 'success'
                    elif equipement['statut'] == 'maintenance':
                        equipement['statut_affichage'] = 'En maintenance'
                        equipement['classe_statut'] = 'warning'
                    elif equipement['statut'] == 'panne':
                        equipement['statut_affichage'] = 'En panne'
                        equipement['classe_statut'] = 'danger'
                    else:
                        equipement['statut_affichage'] = 'Inactif'
                        equipement['classe_statut'] = 'secondary'
                
        except Exception as e:
            flash(f'Erreur lors de la récupération des équipements: {str(e)}', 'danger')
            logger.error(f"Erreur liste équipements: {str(e)}")
        finally:
            conn.close()
    
    return render_template('maintenance/equipements.html', 
                          equipements=equipements,
                          lignes=lignes if 'lignes' in locals() else [],
                          filtres={
                              'ligne_id': ligne_id,
                              'statut': statut
                          })

@app.route('/maintenance/equipements/<int:equipement_id>')
@login_required
@log_activity('details_equipement')
def maintenance_equipement_details(equipement_id):
    """Détails d'un équipement et historique de maintenance."""
    conn = get_db_connection()
    equipement = None
    maintenances = []
    interventions = []
    stats = {}
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Détails de l'équipement
                sql = """
                SELECT e.*, l.nom as ligne_nom, u.prenom, u.nom as nom_utilisateur
                FROM equipements e
                LEFT JOIN lignes_production l ON e.ligne_production_id = l.id
                LEFT JOIN utilisateurs u ON e.utilisateur_id = u.id
                WHERE e.id = %s
                """
                cursor.execute(sql, (equipement_id,))
                equipement = cursor.fetchone()
                
                if not equipement:
                    flash('Équipement non trouvé', 'warning')
                    return redirect(url_for('maintenance_equipements'))
                
                # Statut pour affichage
                if equipement['statut'] == 'operationnel':
                    equipement['statut_affichage'] = 'Opérationnel'
                    equipement['classe_statut'] = 'success'
                elif equipement['statut'] == 'maintenance':
                    equipement['statut_affichage'] = 'En maintenance'
                    equipement['classe_statut'] = 'warning'
                elif equipement['statut'] == 'panne':
                    equipement['statut_affichage'] = 'En panne'
                    equipement['classe_statut'] = 'danger'
                else:
                    equipement['statut_affichage'] = 'Inactif'
                    equipement['classe_statut'] = 'secondary'
                
                # Historique des maintenances
                sql = """
                SELECT m.*, t.nom as type_nom, u.prenom, u.nom as nom_utilisateur
                FROM maintenance m
                JOIN types_maintenance t ON m.type_maintenance_id = t.id
                JOIN utilisateurs u ON m.utilisateur_id = u.id
                WHERE m.equipement_id = %s
                ORDER BY m.date_programmee DESC
                LIMIT 20
                """
                cursor.execute(sql, (equipement_id,))
                maintenances = cursor.fetchall()
                
                # Formater les maintenances
                for m in maintenances:
                    if m['statut'] == 'en_cours':
                        m['statut_affichage'] = 'En cours'
                        m['classe_statut'] = 'warning'
                    elif m['statut'] == 'planifie':
                        m['statut_affichage'] = 'Planifiée'
                        m['classe_statut'] = 'info'
                    elif m['statut'] == 'terminee':
                        m['statut_affichage'] = 'Terminée'
                        m['classe_statut'] = 'success'
                    else:
                        m['statut_affichage'] = 'Annulée'
                        m['classe_statut'] = 'danger'
                
                # Interventions récentes
                sql = """
                SELECT i.*, m.type_maintenance_id, t.nom as type_nom, u.prenom, u.nom as nom_utilisateur
                FROM interventions i
                JOIN maintenance m ON i.maintenance_id = m.id
                JOIN types_maintenance t ON m.type_maintenance_id = t.id
                JOIN utilisateurs u ON i.utilisateur_id = u.id
                WHERE m.equipement_id = %s
                ORDER BY i.date_intervention DESC
                LIMIT 10
                """
                cursor.execute(sql, (equipement_id,))
                interventions = cursor.fetchall()
                
                # Statistiques de maintenance
                cursor.execute("""
                    SELECT 
                        COUNT(*) as total_maintenance,
                        SUM(CASE WHEN statut = 'terminee' THEN 1 ELSE 0 END) as nb_terminees,
                        SUM(CASE WHEN statut = 'en_cours' THEN 1 ELSE 0 END) as nb_en_cours,
                        SUM(CASE WHEN statut = 'planifie' THEN 1 ELSE 0 END) as nb_planifiees,
                        AVG(CASE WHEN statut = 'terminee' AND date_fin IS NOT NULL THEN 
                            TIMESTAMPDIFF(HOUR, date_programmee, date_fin) ELSE NULL END) as duree_moyenne,
                        MAX(date_fin) as derniere_maintenance
                    FROM maintenance
                    WHERE equipement_id = %s
                """, (equipement_id,))
                stats = cursor.fetchone()
                
                # Statistiques par type de maintenance
                cursor.execute("""
                    SELECT t.nom, COUNT(*) as nombre
                    FROM maintenance m
                    JOIN types_maintenance t ON m.type_maintenance_id = t.id
                    WHERE m.equipement_id = %s
                    GROUP BY t.nom
                    ORDER BY nombre DESC
                """, (equipement_id,))
                stats_types = cursor.fetchall()
                
                # Créer un graphique pour les types de maintenance
                if stats_types:
                    plt.figure(figsize=(8, 6))
                    
                    types = [t['nom'] for t in stats_types]
                    nombres = [t['nombre'] for t in stats_types]
                    
                    plt.bar(types, nombres)
                    plt.title('Répartition des maintenances par type')
                    plt.xlabel('Type de maintenance')
                    plt.ylabel('Nombre')
                    plt.xticks(rotation=45)
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    equipement['graphique_types'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
                # Pièces les plus remplacées
                cursor.execute("""
                    SELECT pieces_remplacees
                    FROM interventions i
                    JOIN maintenance m ON i.maintenance_id = m.id
                    WHERE m.equipement_id = %s AND i.pieces_remplacees IS NOT NULL AND i.pieces_remplacees != ''
                """, (equipement_id,))
                
                pieces_data = cursor.fetchall()
                pieces_list = []
                for p in pieces_data:
                    if p['pieces_remplacees']:
                        pieces = p['pieces_remplacees'].split(',')
                        pieces_list.extend([piece.strip() for piece in pieces if piece.strip()])
                
                pieces_counter = {}
                for piece in pieces_list:
                    if piece in pieces_counter:
                        pieces_counter[piece] += 1
                    else:
                        pieces_counter[piece] = 1
                
                # Trier par fréquence
                pieces_counter = dict(sorted(pieces_counter.items(), key=lambda item: item[1], reverse=True))
                equipement['pieces_frequentes'] = pieces_counter
                
        except Exception as e:
            flash(f'Erreur lors de la récupération des détails de l\'équipement: {str(e)}', 'danger')
            logger.error(f"Erreur détails équipement {equipement_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('maintenance/equipement_details.html', 
                          equipement=equipement, 
                          maintenances=maintenances,
                          interventions=interventions,
                          stats=stats,
                          stats_types=stats_types if 'stats_types' in locals() else [])

# =============================================================================
# GESTION DE LA QUALITÉ
# =============================================================================

@app.route('/qualite')
@login_required
@log_activity('liste_qualite')
def qualite_liste():
    """Liste des contrôles qualité."""
    conn = get_db_connection()
    controles = []
    
    # Paramètres de filtrage
    produit_id = request.args.get('produit_id', type=int)
    resultat = request.args.get('resultat')
    type_controle = request.args.get('type_controle')
    date_debut = request.args.get('date_debut')
    date_fin = request.args.get('date_fin')
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Listes pour les filtres
                cursor.execute("SELECT id, nom, reference FROM produits WHERE actif = 1 ORDER BY nom")
                produits = cursor.fetchall()
                
                cursor.execute("SELECT DISTINCT type_controle FROM controles_qualite ORDER BY type_controle")
                types_controle = cursor.fetchall()
                
                # Construction de la requête
                sql = """
                SELECT c.*, p.nom as produit_nom, p.reference,
                       u.prenom, u.nom as nom_utilisateur
                FROM controles_qualite c
                JOIN produits p ON c.produit_id = p.id
                JOIN utilisateurs u ON c.utilisateur_id = u.id
                WHERE 1=1
                """
                params = []
                
                # Ajout des filtres
                if produit_id:
                    sql += " AND c.produit_id = %s"
                    params.append(produit_id)
                
                if resultat:
                    sql += " AND c.resultat = %s"
                    params.append(resultat)
                
                if type_controle:
                    sql += " AND c.type_controle = %s"
                    params.append(type_controle)
                
                if date_debut:
                    sql += " AND c.date_controle >= %s"
                    params.append(f"{date_debut} 00:00:00")
                
                if date_fin:
                    sql += " AND c.date_controle <= %s"
                    params.append(f"{date_fin} 23:59:59")
                
                # Tri par défaut
                sql += " ORDER BY c.date_controle DESC LIMIT 100"
                
                cursor.execute(sql, params)
                controles = cursor.fetchall()
                
                # Formater les résultats pour l'affichage
                for c in controles:
                    if c['resultat'] == 'conforme':
                        c['resultat_affichage'] = 'Conforme'
                        c['classe_resultat'] = 'success'
                    elif c['resultat'] == 'non_conforme':
                        c['resultat_affichage'] = 'Non conforme'
                        c['classe_resultat'] = 'danger'
                    else:
                        c['resultat_affichage'] = 'En attente'
                        c['classe_resultat'] = 'warning'
                
                # Statistiques générales
                cursor.execute("""
                    SELECT 
                        COUNT(*) as total,
                        SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) as nb_conformes,
                        SUM(CASE WHEN resultat = 'non_conforme' THEN 1 ELSE 0 END) as nb_non_conformes,
                        ROUND(SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) / COUNT(*) * 100, 2) as taux_conformite
                    FROM controles_qualite
                    WHERE date_controle >= DATE_SUB(NOW(), INTERVAL 30 DAY)
                """)
                statistiques = cursor.fetchone()
                
        except Exception as e:
            flash(f'Erreur lors de la récupération des contrôles qualité: {str(e)}', 'danger')
            logger.error(f"Erreur liste qualité: {str(e)}")
        finally:
            conn.close()
    
    return render_template('qualite/liste.html', 
                          controles=controles,
                          produits=produits if 'produits' in locals() else [],
                          types_controle=types_controle if 'types_controle' in locals() else [],
                          statistiques=statistiques if 'statistiques' in locals() else None,
                          resultats=[
                              {'code': 'conforme', 'nom': 'Conforme'},
                              {'code': 'non_conforme', 'nom': 'Non conforme'},
                              {'code': 'en_attente', 'nom': 'En attente'}
                          ],
                          filtres={
                              'produit_id': produit_id,
                              'resultat': resultat,
                              'type_controle': type_controle,
                              'date_debut': date_debut,
                              'date_fin': date_fin
                          })

@app.route('/qualite/ajouter', methods=['GET', 'POST'])
@login_required
@role_required('operator')
@log_activity('ajout_qualite')
def qualite_ajouter():
    """Ajout d'un contrôle qualité."""
    today = datetime.now().strftime('%Y-%m-%d')  # Format for HTML date input
    conn = get_db_connection()
    produits = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Liste des produits
                cursor.execute("SELECT id, nom, reference FROM produits WHERE actif = 1 ORDER BY nom")
                produits = cursor.fetchall()
                
                # Liste des lots récents
                cursor.execute("""
                    SELECT p.id, p.numero_lot, pr.nom as produit_nom, pr.reference
                    FROM production p
                    JOIN produits pr ON p.produit_id = pr.id
                    WHERE p.date_creation >= DATE_SUB(NOW(), INTERVAL 30 DAY)
                    ORDER BY p.date_creation DESC
                    LIMIT 50
                """)
                lots = cursor.fetchall()
                
                if request.method == 'POST':
                    produit_id = request.form.get('produit_id')
                    lot_id = request.form.get('lot_id')
                    numero_lot = request.form.get('numero_lot')
                    numero_serie = request.form.get('numero_serie')
                    type_controle = request.form.get('type_controle')
                    resultat = request.form.get('resultat')
                    commentaire = request.form.get('commentaire')
                    mesures = request.form.get('mesures', '{}')
                    
                    # Validation
                    if not all([produit_id, type_controle, resultat]):
                        flash('Tous les champs obligatoires doivent être remplis', 'danger')
                        return render_template('qualite/ajouter.html', produits=produits, lots=lots)
                    
                    # Si aucun lot ou numéro de série spécifié, utiliser "SANS_LOT"
                    if not lot_id and not numero_lot and not numero_serie:
                        numero_lot = f"SANS_LOT_{datetime.now().strftime('%Y%m%d')}"
                    
                    # Traitement des mesures (conversion en JSON si fourni)
                    try:
                        if mesures and mesures.strip() != '{}':
                            json.loads(mesures)  # Validation du format JSON
                    except:
                        mesures = '{}'
                        flash('Format des mesures incorrect, elles ont été ignorées', 'warning')
                    
                    # Gérer le téléchargement d'un rapport si présent
                    rapport_url = None
                    if 'rapport' in request.files:
                        rapport_file = request.files['rapport']
                        if rapport_file and rapport_file.filename != '' and allowed_file(rapport_file.filename):
                            secure_name = sanitize_filename(rapport_file.filename)
                            unique_filename = generate_unique_filename(secure_name)
                            
                            rapport_dir = os.path.join(app.config['UPLOAD_FOLDER'], 'qualite')
                            os.makedirs(rapport_dir, exist_ok=True)
                            
                            filepath = os.path.join(rapport_dir, unique_filename)
                            rapport_file.save(filepath)
                            rapport_url = f"/static/uploads/qualite/{unique_filename}"
                    
                    # Enregistrer le contrôle qualité
                    cursor.execute("""
                        INSERT INTO controles_qualite 
                        (produit_id, lot_id, numero_lot, numero_serie, type_controle, resultat, 
                        commentaire, mesures, rapport_url, utilisateur_id, date_controle)
                        VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                    """, (
                        produit_id, lot_id, numero_lot, numero_serie, type_controle, resultat, 
                        commentaire, mesures, rapport_url, session['user_id'], datetime.now()
                    ))
                    controle_id = cursor.lastrowid
                    conn.commit()
                    
                    # Récupérer les informations du produit pour le log
                    cursor.execute("SELECT nom, reference FROM produits WHERE id = %s", (produit_id,))
                    produit_info = cursor.fetchone()
                    
                    log_message = f"Contrôle qualité ajouté: {produit_info['nom']} ({produit_info['reference']}) - {resultat}"
                    flash('Contrôle qualité ajouté avec succès', 'success')
                    logger.info(log_message)
                    
                    # Si non conforme, notifier les responsables qualité
                    if resultat == 'non_conforme':
                        # Récupérer les emails des responsables qualité
                        cursor.execute("""
                            SELECT email FROM utilisateurs 
                            WHERE role IN ('supervisor', 'manager', 'admin') AND actif = 1
                        """)
                        emails = [row['email'] for row in cursor.fetchall()]
                        
                        if emails:
                            lot_info = f"Lot: {numero_lot}" if numero_lot else f"N° Série: {numero_serie}" if numero_serie else ""
                            
                            sujet = f"Alerte qualité: {produit_info['nom']} ({produit_info['reference']})"
                            corps = f"""
                            Un contrôle qualité non conforme a été détecté:
                            
                            Produit: {produit_info['nom']} ({produit_info['reference']})
                            {lot_info}
                            Type de contrôle: {type_controle}
                            
                            Commentaire: {commentaire}
                            
                            Veuillez vérifier le rapport complet dans le système.
                            """
                            
                            send_notification_email(sujet, emails, corps)
                    
                    return redirect(url_for('qualite_details', controle_id=controle_id))
                
        except Exception as e:
            flash(f'Erreur lors de l\'ajout du contrôle qualité: {str(e)}', 'danger')
            logger.error(f"Erreur ajout qualité: {str(e)}")
        finally:
            conn.close()
    
    return render_template('qualite/ajouter.html', produits=produits, lots=lots if 'lots' in locals() else [])

@app.route('/qualite/<int:controle_id>')
@login_required
@log_activity('details_qualite')
def qualite_details(controle_id):
    """Détails d'un contrôle qualité."""
    conn = get_db_connection()
    controle = None
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer les détails du contrôle
                sql = """
                SELECT c.*, p.nom as produit_nom, p.reference, p.categorie,
                       u.prenom, u.nom as nom_utilisateur
                FROM controles_qualite c
                JOIN produits p ON c.produit_id = p.id
                JOIN utilisateurs u ON c.utilisateur_id = u.id
                WHERE c.id = %s
                """
                cursor.execute(sql, (controle_id,))
                controle = cursor.fetchone()
                
                if not controle:
                    flash('Contrôle qualité non trouvé', 'warning')
                    return redirect(url_for('qualite_liste'))
                
                # Formater pour l'affichage
                if controle['resultat'] == 'conforme':
                    controle['resultat_affichage'] = 'Conforme'
                    controle['classe_resultat'] = 'success'
                elif controle['resultat'] == 'non_conforme':
                    controle['resultat_affichage'] = 'Non conforme'
                    controle['classe_resultat'] = 'danger'
                else:
                    controle['resultat_affichage'] = 'En attente'
                    controle['classe_resultat'] = 'warning'
                
                # Convertir les mesures JSON en dictionnaire pour l'affichage
                if controle['mesures']:
                    try:
                        controle['mesures_dict'] = json.loads(controle['mesures'])
                    except:
                        controle['mesures_dict'] = {}
                
                # Récupérer le lot associé si existant
                if controle['lot_id']:
                    cursor.execute("""
                        SELECT p.*, l.nom as ligne_nom
                        FROM production p
                        JOIN lignes_production l ON p.ligne_production_id = l.id
                        WHERE p.id = %s
                    """, (controle['lot_id'],))
                    controle['lot_info'] = cursor.fetchone()
                
                # Autres contrôles du même lot/numéro de série
                autres_controles = []
                if controle['numero_lot']:
                    cursor.execute("""
                        SELECT c.id, c.type_controle, c.resultat, c.date_controle
                        FROM controles_qualite c
                        WHERE c.numero_lot = %s AND c.id != %s
                        ORDER BY c.date_controle DESC
                    """, (controle['numero_lot'], controle_id))
                    autres_controles = cursor.fetchall()
                elif controle['numero_serie']:
                    cursor.execute("""
                        SELECT c.id, c.type_controle, c.resultat, c.date_controle
                        FROM controles_qualite c
                        WHERE c.numero_serie = %s AND c.id != %s
                        ORDER BY c.date_controle DESC
                    """, (controle['numero_serie'], controle_id))
                    autres_controles = cursor.fetchall()
                
                controle['autres_controles'] = autres_controles
                
        except Exception as e:
            flash(f'Erreur lors de la récupération des détails du contrôle: {str(e)}', 'danger')
            logger.error(f"Erreur détails qualité {controle_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('qualite/details.html', controle=controle)

@app.route('/qualite/<int:controle_id>/modifier', methods=['GET', 'POST'])
@login_required
@role_required('supervisor')
@log_activity('modification_qualite')
@audit_trail('controles_qualite')
def qualite_modifier(controle_id):
    """Modification d'un contrôle qualité."""
    conn = get_db_connection()
    controle = None
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer le contrôle
                cursor.execute("SELECT * FROM controles_qualite WHERE id = %s", (controle_id,))
                controle = cursor.fetchone()
                
                if not controle:
                    flash('Contrôle qualité non trouvé', 'warning')
                    return redirect(url_for('qualite_liste'))
                
                # Récupérer les détails du produit
                cursor.execute("SELECT nom, reference FROM produits WHERE id = %s", (controle['produit_id'],))
                produit = cursor.fetchone()
                if produit:
                    controle['produit_nom'] = produit['nom']
                    controle['reference'] = produit['reference']
                
                if request.method == 'POST':
                    type_controle = request.form.get('type_controle')
                    resultat = request.form.get('resultat')
                    commentaire = request.form.get('commentaire')
                    mesures = request.form.get('mesures', '{}')
                    
                    # Validation du format JSON pour les mesures
                    try:
                        if mesures and mesures.strip() != '{}':
                            json.loads(mesures)
                    except:
                        mesures = '{}'
                        flash('Format des mesures incorrect, elles ont été ignorées', 'warning')
                    
                    # Gérer le téléchargement d'un nouveau rapport si présent
                    rapport_url = controle['rapport_url']
                    if 'rapport' in request.files:
                        rapport_file = request.files['rapport']
                        if rapport_file and rapport_file.filename != '' and allowed_file(rapport_file.filename):
                            # Supprimer l'ancien rapport si présent
                            if rapport_url:
                                ancien_fichier = os.path.join(app.root_path, rapport_url.lstrip('/'))
                                if os.path.exists(ancien_fichier):
                                    os.remove(ancien_fichier)
                            
                            # Enregistrer le nouveau rapport
                            secure_name = sanitize_filename(rapport_file.filename)
                            unique_filename = generate_unique_filename(secure_name)
                            
                            rapport_dir = os.path.join(app.config['UPLOAD_FOLDER'], 'qualite')
                            os.makedirs(rapport_dir, exist_ok=True)
                            
                            filepath = os.path.join(rapport_dir, unique_filename)
                            rapport_file.save(filepath)
                            rapport_url = f"/static/uploads/qualite/{unique_filename}"
                    
                    # Mise à jour du contrôle
                    cursor.execute("""
                        UPDATE controles_qualite 
                        SET type_controle = %s, resultat = %s, commentaire = %s, mesures = %s, 
                            rapport_url = %s, date_modification = %s
                        WHERE id = %s
                    """, (
                        type_controle, resultat, commentaire, mesures, 
                        rapport_url, datetime.now(), controle_id
                    ))
                    conn.commit()
                    
                    # Si changement de résultat vers non conforme, notifier
                    if resultat == 'non_conforme' and controle['resultat'] != 'non_conforme':
                        cursor.execute("""
                            SELECT email FROM utilisateurs 
                            WHERE role IN ('supervisor', 'manager', 'admin') AND actif = 1
                        """)
                        emails = [row['email'] for row in cursor.fetchall()]
                        
                        if emails:
                            lot_info = f"Lot: {controle['numero_lot']}" if controle['numero_lot'] else f"N° Série: {controle['numero_serie']}" if controle['numero_serie'] else ""
                            
                            sujet = f"Changement statut qualité: {controle['produit_nom']} ({controle['reference']})"
                            corps = f"""
                            Un contrôle qualité a été modifié en "Non conforme":
                            
                            Produit: {controle['produit_nom']} ({controle['reference']})
                            {lot_info}
                            Type de contrôle: {type_controle}
                            Date du contrôle: {controle['date_controle'].strftime('%d/%m/%Y %H:%M')}
                            
                            Commentaire: {commentaire}
                            
                            Veuillez vérifier le rapport complet dans le système.
                            """
                            
                            send_notification_email(sujet, emails, corps)
                    
                    flash('Contrôle qualité modifié avec succès', 'success')
                    logger.info(f"Contrôle qualité modifié: ID {controle_id}")
                    return redirect(url_for('qualite_details', controle_id=controle_id))
                
        except Exception as e:
            flash(f'Erreur lors de la modification du contrôle qualité: {str(e)}', 'danger')
            logger.error(f"Erreur modification qualité {controle_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('qualite/modifier.html', controle=controle)

@app.route('/qualite/normes')
@login_required
@log_activity('liste_normes')
def qualite_normes():
    """Liste des normes et standards de qualité."""
    conn = get_db_connection()
    normes = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer les normes
                sql = """
                SELECT n.*, u.prenom, u.nom as nom_utilisateur,
                       (SELECT COUNT(*) FROM normes_produits WHERE norme_id = n.id) as nb_produits
                FROM normes n
                JOIN utilisateurs u ON n.utilisateur_id = u.id
                ORDER BY n.categorie, n.code
                """
                cursor.execute(sql)
                normes = cursor.fetchall()
                
                # Récupérer les catégories pour filtrage
                cursor.execute("SELECT DISTINCT categorie FROM normes ORDER BY categorie")
                categories = cursor.fetchall()
                
        except Exception as e:
            flash(f'Erreur lors de la récupération des normes: {str(e)}', 'danger')
            logger.error(f"Erreur liste normes: {str(e)}")
        finally:
            conn.close()
    
    return render_template('qualite/normes.html', normes=normes, categories=categories if 'categories' in locals() else [])

@app.route('/qualite/normes/<int:norme_id>')
@login_required
@log_activity('details_norme')
def qualite_norme_details(norme_id):
    """Détails d'une norme de qualité."""
    conn = get_db_connection()
    norme = None
    produits = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer les détails de la norme
                sql = """
                SELECT n.*, u.prenom, u.nom as nom_utilisateur
                FROM normes n
                JOIN utilisateurs u ON n.utilisateur_id = u.id
                WHERE n.id = %s
                """
                cursor.execute(sql, (norme_id,))
                norme = cursor.fetchone()
                
                if not norme:
                    flash('Norme non trouvée', 'warning')
                    return redirect(url_for('qualite_normes'))
                
                # Récupérer les produits associés à cette norme
                sql = """
                SELECT p.id, p.nom, p.reference, p.categorie
                FROM normes_produits np
                JOIN produits p ON np.produit_id = p.id
                WHERE np.norme_id = %s AND p.actif = 1
                ORDER BY p.nom
                """
                cursor.execute(sql, (norme_id,))
                produits = cursor.fetchall()
                
                # Récupérer les spécifications de la norme
                sql = """
                SELECT * FROM specifications 
                WHERE norme_id = %s
                ORDER BY nom
                """
                cursor.execute(sql, (norme_id,))
                specifications = cursor.fetchall()
                
        except Exception as e:
            flash(f'Erreur lors de la récupération des détails de la norme: {str(e)}', 'danger')
            logger.error(f"Erreur détails norme {norme_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('qualite/norme_details.html', 
                          norme=norme, 
                          produits=produits,
                          specifications=specifications if 'specifications' in locals() else [])

@app.route('/qualite/rapport')
@login_required
@role_required('supervisor')
@log_activity('rapport_qualite')
def qualite_rapport():
    """Génération de rapports d'analyse de la qualité."""
    conn = get_db_connection()
    statistiques = {}
    graphiques = {}
    
    # Paramètres de filtrage
    date_debut = request.args.get('date_debut', (datetime.now() - timedelta(days=30)).strftime('%Y-%m-%d'))
    date_fin = request.args.get('date_fin', datetime.now().strftime('%Y-%m-%d'))
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Statistiques générales
                sql = """
                SELECT 
                    COUNT(*) as total_controles,
                    SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) as conformes,
                    SUM(CASE WHEN resultat = 'non_conforme' THEN 1 ELSE 0 END) as non_conformes,
                    ROUND(SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) / COUNT(*) * 100, 2) as taux_conformite
                FROM controles_qualite
                WHERE date_controle BETWEEN %s AND %s
                """
                cursor.execute(sql, (f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"))
                statistiques['global'] = cursor.fetchone()
                
                # Données par produit
                sql = """
                SELECT p.id, p.nom, p.reference,
                    COUNT(*) as total_controles,
                    SUM(CASE WHEN c.resultat = 'conforme' THEN 1 ELSE 0 END) as conformes,
                    SUM(CASE WHEN c.resultat = 'non_conforme' THEN 1 ELSE 0 END) as non_conformes,
                    ROUND(SUM(CASE WHEN c.resultat = 'conforme' THEN 1 ELSE 0 END) / COUNT(*) * 100, 2) as taux_conformite
                FROM controles_qualite c
                JOIN produits p ON c.produit_id = p.id
                WHERE c.date_controle BETWEEN %s AND %s
                GROUP BY p.id, p.nom, p.reference
                ORDER BY taux_conformite ASC
                LIMIT 20
                """
                cursor.execute(sql, (f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"))
                statistiques['produits'] = cursor.fetchall()
                
                # Données par type de contrôle
                sql = """
                SELECT type_controle,
                    COUNT(*) as total_controles,
                    SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) as conformes,
                    SUM(CASE WHEN resultat = 'non_conforme' THEN 1 ELSE 0 END) as non_conformes,
                    ROUND(SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) / COUNT(*) * 100, 2) as taux_conformite
                FROM controles_qualite
                WHERE date_controle BETWEEN %s AND %s
                GROUP BY type_controle
                ORDER BY taux_conformite ASC
                """
                cursor.execute(sql, (f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"))
                statistiques['types'] = cursor.fetchall()
                
                # Évolution de la qualité dans le temps
                sql = """
                SELECT DATE_FORMAT(date_controle, '%Y-%m-%d') as date,
                       COUNT(*) as total,
                       SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) as conformes,
                       ROUND(SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) / COUNT(*) * 100, 2) as taux
                FROM controles_qualite
                WHERE date_controle BETWEEN %s AND %s
                GROUP BY DATE_FORMAT(date_controle, '%Y-%m-%d')
                ORDER BY date
                """
                cursor.execute(sql, (f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"))
                evolution_data = cursor.fetchall()
                
                # Création des graphiques
                if statistiques['produits']:
                    plt.figure(figsize=(12, 6))
                    
                    produits = [f"{p['nom']} ({p['reference']})" for p in statistiques['produits'][:10]]
                    taux = [p['taux_conformite'] for p in statistiques['produits'][:10]]
                    
                    bars = plt.barh(produits, taux, color='green')
                    plt.axvline(x=95, color='red', linestyle='--', label='Seuil acceptable (95%)')
                    
                    # Ajouter les valeurs sur les barres
                    for i, bar in enumerate(bars):
                        plt.text(bar.get_width() + 1, bar.get_y() + bar.get_height()/2, 
                                f"{taux[i]}%", va='center')
                    
                    plt.title('Taux de conformité par produit')
                    plt.xlabel('Taux de conformité (%)')
                    plt.ylabel('Produit')
                    plt.legend()
                    plt.grid(True, linestyle='--', alpha=0.7)
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    graphiques['produits'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
                if evolution_data:
                    plt.figure(figsize=(12, 6))
                    
                    dates = [item['date'] for item in evolution_data]
                    taux = [item['taux'] for item in evolution_data]
                    
                    plt.plot(dates, taux, marker='o', linestyle='-', color='blue')
                    plt.axhline(y=95, color='red', linestyle='--', label='Seuil acceptable (95%)')
                    
                    plt.title('Évolution du taux de conformité')
                    plt.xlabel('Date')
                    plt.ylabel('Taux de conformité (%)')
                    plt.legend()
                    plt.grid(True, linestyle='--', alpha=0.7)
                    plt.xticks(rotation=45)
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    graphiques['evolution'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
                if statistiques['types']:
                    plt.figure(figsize=(10, 6))
                    
                    types = [item['type_controle'] for item in statistiques['types']]
                    conformes = [item['conformes'] for item in statistiques['types']]
                    non_conformes = [item['non_conformes'] for item in statistiques['types']]
                    
                    ind = np.arange(len(types))
                    width = 0.35
                    
                    p1 = plt.bar(ind, conformes, width, color='green')
                    p2 = plt.bar(ind, non_conformes, width, bottom=conformes, color='red')
                    
                    plt.ylabel('Nombre de contrôles')
                    plt.title('Contrôles par type')
                    plt.xticks(ind, types, rotation=45)
                    plt.legend((p1[0], p2[0]), ('Conformes', 'Non conformes'))
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    graphiques['types'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
        except Exception as e:
            flash(f'Erreur lors de la génération du rapport: {str(e)}', 'danger')
            logger.error(f"Erreur rapport qualité: {str(e)}")
        finally:
            conn.close()
    
    return render_template('qualite/rapport.html', 
                          statistiques=statistiques, 
                          graphiques=graphiques,
                          date_debut=date_debut,
                          date_fin=date_fin)

# =============================================================================
# GESTION DES RAPPORTS ET STATISTIQUES
# =============================================================================

@app.route('/rapports')
@login_required
@role_required('supervisor')
@log_activity('menu_rapports')
def rapports_liste():
    """Menu principal des rapports disponibles."""
    conn = get_db_connection()
    rapports = []
    utilisateurs = []
    stats = {
        'total': 0,
        'production': 0,
        'maintenance': 0,
        'qualite': 0,
        'kpi': 0
    }
    
    # Variables pour les graphiques d'évolution
    evolution_labels = []
    evolution_production = []
    evolution_maintenance = []
    evolution_qualite = []
    evolution_kpi = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Liste des utilisateurs pour le filtre
                cursor.execute("""
                    SELECT id, nom, prenom FROM utilisateurs 
                    WHERE actif = 1 AND role IN ('supervisor', 'manager', 'admin')
                    ORDER BY nom, prenom
                """)
                utilisateurs = cursor.fetchall()
                
                # Récupérer les statistiques des rapports
                cursor.execute("""
                    SELECT COUNT(*) as total,
                           SUM(CASE WHEN type = 'production' THEN 1 ELSE 0 END) as production,
                           SUM(CASE WHEN type = 'maintenance' THEN 1 ELSE 0 END) as maintenance,
                           SUM(CASE WHEN type = 'qualite' THEN 1 ELSE 0 END) as qualite,
                           SUM(CASE WHEN type = 'kpi' THEN 1 ELSE 0 END) as kpi
                    FROM rapports
                """)
                stats_result = cursor.fetchone()
                if stats_result:
                    stats = stats_result
                
                # Récupérer les données d'évolution sur 6 derniers mois
                cursor.execute("""
                    SELECT DATE_FORMAT(date_creation, '%Y-%m') as mois
                    FROM rapports
                    WHERE date_creation >= DATE_SUB(NOW(), INTERVAL 6 MONTH)
                    GROUP BY mois
                    ORDER BY mois
                """)
                months = cursor.fetchall()
                evolution_labels = [month['mois'] for month in months]
                
                # Pour chaque mois, récupérer le nombre de rapports par type
                for month in evolution_labels:
                    # Production
                    cursor.execute("""
                        SELECT COUNT(*) as count
                        FROM rapports
                        WHERE DATE_FORMAT(date_creation, '%Y-%m') = %s AND type = 'production'
                    """, (month,))
                    evolution_production.append(cursor.fetchone()['count'])
                    
                    # Maintenance
                    cursor.execute("""
                        SELECT COUNT(*) as count
                        FROM rapports
                        WHERE DATE_FORMAT(date_creation, '%Y-%m') = %s AND type = 'maintenance'
                    """, (month,))
                    evolution_maintenance.append(cursor.fetchone()['count'])
                    
                    # Qualité
                    cursor.execute("""
                        SELECT COUNT(*) as count
                        FROM rapports
                        WHERE DATE_FORMAT(date_creation, '%Y-%m') = %s AND type = 'qualite'
                    """, (month,))
                    evolution_qualite.append(cursor.fetchone()['count'])
                    
                    # KPI
                    cursor.execute("""
                        SELECT COUNT(*) as count
                        FROM rapports
                        WHERE DATE_FORMAT(date_creation, '%Y-%m') = %s AND type = 'kpi'
                    """, (month,))
                    evolution_kpi.append(cursor.fetchone()['count'])
                
                # Récupérer la liste des rapports avec filtres
                sql = """
                    SELECT r.*, u.nom as auteur_nom, u.prenom as auteur_prenom
                    FROM rapports r
                    LEFT JOIN utilisateurs u ON r.utilisateur_id = u.id
                    WHERE 1=1
                """
                params = []
                
                # Appliquer les filtres si présents
                if request.args.get('date_debut'):
                    sql += " AND r.date_debut >= %s"
                    params.append(request.args.get('date_debut'))
                
                if request.args.get('date_fin'):
                    sql += " AND r.date_fin <= %s"
                    params.append(request.args.get('date_fin'))
                
                if request.args.get('type_rapport'):
                    sql += " AND r.type = %s"
                    params.append(request.args.get('type_rapport'))
                
                if request.args.get('auteur'):
                    sql += " AND r.utilisateur_id = %s"
                    params.append(request.args.get('auteur'))
                
                sql += " ORDER BY r.date_creation DESC"
                cursor.execute(sql, params)
                rapports = cursor.fetchall()
                
        except Exception as e:
            flash(f'Erreur lors du chargement des rapports: {str(e)}', 'danger')
            logger.error(f"Erreur liste rapports: {str(e)}")
        finally:
            conn.close()
    
    # Définir des valeurs par défaut si les listes sont vides
    if not evolution_labels:
        evolution_labels = [datetime.now().strftime('%Y-%m')]
        evolution_production = [0]
        evolution_maintenance = [0]
        evolution_qualite = [0]
        evolution_kpi = [0]
    
    return render_template('rapports/liste.html', 
                          rapports=rapports,
                          utilisateurs=utilisateurs,
                          stats=stats,
                          evolution_labels=evolution_labels,
                          evolution_production=evolution_production,
                          evolution_maintenance=evolution_maintenance,
                          evolution_qualite=evolution_qualite,
                          evolution_kpi=evolution_kpi)

@app.route('/rapports/production', methods=['GET', 'POST'])
@login_required
@role_required('supervisor')
@log_activity('rapport_production')
def rapport_production():
    """Rapport détaillé sur la production."""
    conn = get_db_connection()
    data = {}
    graph_data = None
    
    # Paramètres par défaut
    date_debut = request.args.get('date_debut', (datetime.now() - timedelta(days=30)).strftime('%Y-%m-%d'))
    date_fin = request.args.get('date_fin', datetime.now().strftime('%Y-%m-%d'))
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Données de production par jour
                sql = """
                SELECT DATE(date_creation) as jour, SUM(quantite_produite) as total,
                       COUNT(*) as nb_lots, AVG(temps_production) as temps_moyen
                FROM production
                WHERE date_creation BETWEEN %s AND %s
                GROUP BY jour
                ORDER BY jour
                """
                cursor.execute(sql, (f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"))
                production_jour = cursor.fetchall()
                
                # Données de production par produit
                sql = """
                SELECT p.id, p.nom, p.reference, SUM(pr.quantite_produite) as total,
                       COUNT(*) as nb_lots, AVG(pr.temps_production) as temps_moyen
                FROM production pr
                JOIN produits p ON pr.produit_id = p.id
                WHERE pr.date_creation BETWEEN %s AND %s
                GROUP BY p.id, p.nom, p.reference
                ORDER BY total DESC
                """
                cursor.execute(sql, (f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"))
                production_produit = cursor.fetchall()
                
                # Données de production par ligne
                sql = """
                SELECT l.id, l.nom, SUM(pr.quantite_produite) as total,
                       COUNT(*) as nb_lots, AVG(pr.temps_production) as temps_moyen
                FROM production pr
                JOIN lignes_production l ON pr.ligne_production_id = l.id
                WHERE pr.date_creation BETWEEN %s AND %s
                GROUP BY l.id, l.nom
                ORDER BY total DESC
                """
                cursor.execute(sql, (f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"))
                production_ligne = cursor.fetchall()
                
                # Statistiques de productivité
                sql = """
                SELECT l.nom as ligne_nom, 
                       ROUND(AVG(pr.quantite_produite / pr.temps_production), 2) as productivite_moyenne,
                       ROUND(MAX(pr.quantite_produite / pr.temps_production), 2) as productivite_max
                FROM production pr
                JOIN lignes_production l ON pr.ligne_production_id = l.id
                WHERE pr.date_creation BETWEEN %s AND %s
                AND pr.temps_production > 0
                GROUP BY l.id, l.nom
                ORDER BY productivite_moyenne DESC
                """
                cursor.execute(sql, (f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"))
                productivite = cursor.fetchall()
                
                data = {
                    'production_jour': production_jour,
                    'production_produit': production_produit,
                    'production_ligne': production_ligne,
                    'productivite': productivite
                }
                
                # Génération du graphique de production par jour
                if production_jour:
                    plt.figure(figsize=(12, 6))
                    plt.plot(
                        [item['jour'] for item in production_jour],
                        [item['total'] for item in production_jour],
                        marker='o'
                    )
                    plt.title('Production quotidienne')
                    plt.xlabel('Date')
                    plt.ylabel('Quantité produite')
                    plt.grid(True, linestyle='--', alpha=0.7)
                    plt.xticks(rotation=45)
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    graph_data = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
                # Graphique par produit (top 10)
                if production_produit:
                    plt.figure(figsize=(12, 6))
                    
                    # Limiter aux 10 premiers produits
                    top_produits = production_produit[:10]
                    
                    plt.bar(
                        [f"{item['nom']} ({item['reference']})" for item in top_produits],
                        [item['total'] for item in top_produits]
                    )
                    plt.title('Top 10 des produits par quantité produite')
                    plt.xlabel('Produit')
                    plt.ylabel('Quantité')
                    plt.grid(True, linestyle='--', alpha=0.7)
                    plt.xticks(rotation=45)
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    data['graph_produits'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
                # Graphique de productivité par ligne
                if productivite:
                    plt.figure(figsize=(12, 6))
                    
                    lignes = [item['ligne_nom'] for item in productivite]
                    productivite_moy = [item['productivite_moyenne'] for item in productivite]
                    productivite_max = [item['productivite_max'] for item in productivite]
                    
                    x = np.arange(len(lignes))
                    width = 0.35
                    
                    fig, ax = plt.subplots(figsize=(12, 6))
                    ax.bar(x - width/2, productivite_moy, width, label='Moyenne')
                    ax.bar(x + width/2, productivite_max, width, label='Maximum')
                    
                    ax.set_title('Productivité par ligne de production (unités/heure)')
                    ax.set_xticks(x)
                    ax.set_xticklabels(lignes, rotation=45)
                    ax.legend()
                    ax.grid(True, linestyle='--', alpha=0.7)
                    
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    data['graph_productivite'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
        except Exception as e:
            flash(f'Erreur lors de la génération du rapport: {str(e)}', 'danger')
            logger.error(f"Erreur rapport production: {str(e)}")
        finally:
            conn.close()
    
    return render_template('rapports/production.html', 
                          data=data, 
                          graph_data=graph_data,
                          date_debut=date_debut,
                          date_fin=date_fin)

@app.route('/rapports/maintenance')
@login_required
@role_required('supervisor')
@log_activity('rapport_maintenance')
def rapport_maintenance():
    """Rapport sur les activités de maintenance."""
    conn = get_db_connection()
    data = {}
    graphiques = {}
    
    # Paramètres par défaut
    date_debut = request.args.get('date_debut', (datetime.now() - timedelta(days=90)).strftime('%Y-%m-%d'))
    date_fin = request.args.get('date_fin', datetime.now().strftime('%Y-%m-%d'))
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Statistiques générales
                sql = """
                SELECT 
                    COUNT(*) as total_maintenances,
                    SUM(CASE WHEN statut = 'terminee' THEN 1 ELSE 0 END) as terminees,
                    SUM(CASE WHEN statut = 'en_cours' THEN 1 ELSE 0 END) as en_cours,
                    SUM(CASE WHEN statut = 'planifie' THEN 1 ELSE 0 END) as planifiees,
                    SUM(CASE WHEN statut = 'annulee' THEN 1 ELSE 0 END) as annulees,
                    ROUND(AVG(CASE WHEN statut = 'terminee' AND date_fin IS NOT NULL 
                               THEN TIMESTAMPDIFF(HOUR, date_programmee, date_fin) 
                               ELSE NULL END), 2) as duree_moyenne
                FROM maintenance
                WHERE date_programmee BETWEEN %s AND %s
                """
                cursor.execute(sql, (date_debut, date_fin))
                data['statistiques'] = cursor.fetchone()
                
                # Maintenances par type
                sql = """
                SELECT t.nom, COUNT(*) as nombre,
                       SUM(CASE WHEN m.statut = 'terminee' THEN 1 ELSE 0 END) as terminees,
                       AVG(CASE WHEN m.statut = 'terminee' THEN TIMESTAMPDIFF(HOUR, m.date_programmee, m.date_fin) ELSE NULL END) as duree_moyenne
                FROM maintenance m
                JOIN types_maintenance t ON m.type_maintenance_id = t.id
                WHERE m.date_programmee BETWEEN %s AND %s
                GROUP BY t.id, t.nom
                ORDER BY nombre DESC
                """
                cursor.execute(sql, (date_debut, date_fin))
                data['par_type'] = cursor.fetchall()
                
                # Maintenances par équipement
                sql = """
                SELECT e.nom, COUNT(*) as nombre,
                       SUM(CASE WHEN m.statut = 'terminee' THEN 1 ELSE 0 END) as terminees,
                       SUM(CASE WHEN m.statut = 'annulee' THEN 1 ELSE 0 END) as annulees
                FROM maintenance m
                JOIN equipements e ON m.equipement_id = e.id
                WHERE m.date_programmee BETWEEN %s AND %s
                GROUP BY e.id, e.nom
                ORDER BY nombre DESC
                LIMIT 10
                """
                cursor.execute(sql, (date_debut, date_fin))
                data['par_equipement'] = cursor.fetchall()
                
                # Répartition par priorité
                sql = """
                SELECT priorite, COUNT(*) as nombre
                FROM maintenance
                WHERE date_programmee BETWEEN %s AND %s
                GROUP BY priorite
                ORDER BY CASE 
                    WHEN priorite = 'haute' THEN 1
                    WHEN priorite = 'moyenne' THEN 2
                    ELSE 3
                END
                """
                cursor.execute(sql, (date_debut, date_fin))
                data['par_priorite'] = cursor.fetchall()
                
                # Évolution dans le temps
                sql = """
                SELECT DATE_FORMAT(date_programmee, '%Y-%m') as mois,
                       COUNT(*) as total,
                       SUM(CASE WHEN statut = 'terminee' THEN 1 ELSE 0 END) as terminees,
                       SUM(CASE WHEN statut = 'annulee' THEN 1 ELSE 0 END) as annulees
                FROM maintenance
                WHERE date_programmee BETWEEN DATE_SUB(%s, INTERVAL 6 MONTH) AND %s
                GROUP BY mois
                ORDER BY mois
                """
                cursor.execute(sql, (date_fin, date_fin))
                data['evolution'] = cursor.fetchall()
                
                # Temps moyen de résolution par type
                sql = """
                SELECT t.nom, 
                       ROUND(AVG(CASE WHEN m.statut = 'terminee' AND m.date_fin IS NOT NULL 
                                 THEN TIMESTAMPDIFF(HOUR, m.date_programmee, m.date_fin)
                                 ELSE NULL END), 2) as temps_moyen
                FROM maintenance m
                JOIN types_maintenance t ON m.type_maintenance_id = t.id
                WHERE m.date_programmee BETWEEN %s AND %s
                GROUP BY t.id, t.nom
                HAVING temps_moyen IS NOT NULL
                ORDER BY temps_moyen DESC
                """
                cursor.execute(sql, (date_debut, date_fin))
                data['temps_resolution'] = cursor.fetchall()
                
                # Graphique de répartition par priorité
                if data['par_priorite']:
                    plt.figure(figsize=(8, 8))
                    
                    priorites = [item['priorite'].capitalize() for item in data['par_priorite']]
                    nombres = [item['nombre'] for item in data['par_priorite']]
                    
                    # Définir des couleurs selon la priorité
                    colors = []
                    for p in data['par_priorite']:
                        if p['priorite'] == 'haute':
                            colors.append('red')
                        elif p['priorite'] == 'moyenne':
                            colors.append('orange')
                        else:
                            colors.append('blue')
                    
                    plt.pie(nombres, labels=priorites, autopct='%1.1f%%', colors=colors, startangle=90)
                    plt.title('Répartition des maintenances par priorité')
                    plt.axis('equal')
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    graphiques['priorites'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
                # Graphique d'évolution des maintenances
                if data['evolution']:
                    plt.figure(figsize=(12, 6))
                    
                    mois = [item['mois'] for item in data['evolution']]
                    total = [item['total'] for item in data['evolution']]
                    terminees = [item['terminees'] for item in data['evolution']]
                    annulees = [item['annulees'] for item in data['evolution']]
                    
                    plt.plot(mois, total, 'b-', marker='o', label='Total')
                    plt.plot(mois, terminees, 'g-', marker='s', label='Terminées')
                    plt.plot(mois, annulees, 'r-', marker='x', label='Annulées')
                    
                    plt.title('Évolution des maintenances par mois')
                    plt.xlabel('Mois')
                    plt.ylabel('Nombre de maintenances')
                    plt.grid(True, linestyle='--', alpha=0.7)
                    plt.xticks(rotation=45)
                    plt.legend()
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    graphiques['evolution'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
                # Graphique de temps de résolution par type
                if data['temps_resolution']:
                    plt.figure(figsize=(12, 6))
                    
                    types = [item['nom'] for item in data['temps_resolution']]
                    temps = [item['temps_moyen'] for item in data['temps_resolution']]
                    
                    plt.barh(types, temps)
                    plt.title('Temps moyen de résolution par type de maintenance (heures)')
                    plt.xlabel('Heures')
                    plt.ylabel('Type de maintenance')
                    plt.grid(True, linestyle='--', alpha=0.7)
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    graphiques['temps_resolution'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
        except Exception as e:
            flash(f'Erreur lors de la génération du rapport: {str(e)}', 'danger')
            logger.error(f"Erreur rapport maintenance: {str(e)}")
        finally:
            conn.close()
    
    return render_template('rapports/maintenance.html', 
                          data=data, 
                          graphiques=graphiques,
                          date_debut=date_debut,
                          date_fin=date_fin)

@app.route('/rapports/kpi')
@login_required
@role_required('manager')
@log_activity('rapport_kpi')
def rapport_kpi():
    """Tableau de bord des indicateurs clés de performance."""
    conn = get_db_connection()
    kpis = {}
    graphiques = {}
    
    # Période d'analyse
    periode = request.args.get('periode', 'mois')
    
    if periode == 'semaine':
        date_debut = (datetime.now() - timedelta(days=7)).strftime('%Y-%m-%d')
        periode_texte = "7 derniers jours"
    elif periode == 'trimestre':
        date_debut = (datetime.now() - timedelta(days=90)).strftime('%Y-%m-%d')
        periode_texte = "3 derniers mois"
    elif periode == 'annee':
        date_debut = (datetime.now() - timedelta(days=365)).strftime('%Y-%m-%d')
        periode_texte = "12 derniers mois"
    else:  # mois par défaut
        date_debut = (datetime.now() - timedelta(days=30)).strftime('%Y-%m-%d')
        periode_texte = "30 derniers jours"
    
    date_fin = datetime.now().strftime('%Y-%m-%d')
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # 1. KPI de production
                cursor.execute("""
                    SELECT COUNT(*) as nb_productions,
                           SUM(quantite_produite) as quantite_totale,
                           ROUND(AVG(quantite_produite / temps_production), 2) as productivite_moyenne
                    FROM production
                    WHERE date_creation BETWEEN %s AND %s
                    AND temps_production > 0
                """, (f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"))
                kpis['production'] = cursor.fetchone()
                
                # Productivité par période (jour ou mois selon la période)
                groupe_date = "DATE_FORMAT(date_creation, '%Y-%m-%d')" if periode in ['semaine', 'mois'] else "DATE_FORMAT(date_creation, '%Y-%m')"
                cursor.execute(f"""
                    SELECT {groupe_date} as periode,
                           SUM(quantite_produite) as quantite,
                           ROUND(AVG(quantite_produite / temps_production), 2) as productivite
                    FROM production
                    WHERE date_creation BETWEEN %s AND %s
                    AND temps_production > 0
                    GROUP BY periode
                    ORDER BY periode
                """, (f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"))
                kpis['productivite_periode'] = cursor.fetchall()
                
                # 2. KPI de qualité
                cursor.execute("""
                    SELECT COUNT(*) as nb_controles,
                           SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) as nb_conformes,
                           ROUND(SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) / COUNT(*) * 100, 2) as taux_conformite
                    FROM controles_qualite
                    WHERE date_controle BETWEEN %s AND %s
                """, (f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"))
                kpis['qualite'] = cursor.fetchone()
                
                # 3. KPI de maintenance
                cursor.execute("""
                    SELECT COUNT(*) as nb_maintenances,
                           SUM(CASE WHEN statut = 'terminee' THEN 1 ELSE 0 END) as nb_terminees,
                           SUM(CASE WHEN statut = 'planifie' THEN 1 ELSE 0 END) as nb_planifiees,
                           ROUND(AVG(CASE WHEN statut = 'terminee' AND date_fin IS NOT NULL 
                                     THEN TIMESTAMPDIFF(HOUR, date_programmee, date_fin) 
                                     ELSE NULL END), 2) as temps_moyen_resolution
                    FROM maintenance
                    WHERE date_programmee BETWEEN %s AND %s
                """, (date_debut, date_fin))
                kpis['maintenance'] = cursor.fetchone()
                
                # 4. KPI de stocks
                cursor.execute("""
                    SELECT COUNT(*) as nb_produits_stock,
                           SUM(CASE WHEN s.quantite <= s.seuil_alerte THEN 1 ELSE 0 END) as nb_alertes,
                           ROUND(SUM(CASE WHEN s.quantite <= s.seuil_alerte THEN 1 ELSE 0 END) / COUNT(*) * 100, 2) as pourcentage_alertes
                    FROM stocks s
                    JOIN produits p ON s.produit_id = p.id
                    WHERE s.actif = 1 AND p.actif = 1
                """)
                kpis['stocks'] = cursor.fetchone()
                
                # 5. Performance des lignes de production
                cursor.execute("""
                    SELECT l.nom,
                           SUM(p.quantite_produite) as production_totale,
                           ROUND(AVG(p.quantite_produite / p.temps_production), 2) as performance
                    FROM production p
                    JOIN lignes_production l ON p.ligne_production_id = l.id
                    WHERE p.date_creation BETWEEN %s AND %s
                    AND p.temps_production > 0
                    GROUP BY l.id, l.nom
                    ORDER BY performance DESC
                """, (f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"))
                kpis['performance_lignes'] = cursor.fetchall()
                
                # Créer les graphiques pour le tableau de bord
                
                # Graphique de productivité
                if kpis['productivite_periode']:
                    plt.figure(figsize=(12, 6))
                    
                    periodes = [item['periode'] for item in kpis['productivite_periode']]
                    productivites = [item['productivite'] if item['productivite'] else 0 for item in kpis['productivite_periode']]
                    
                    plt.plot(periodes, productivites, 'b-', marker='o')
                    plt.title(f'Évolution de la productivité ({periode_texte})')
                    plt.xlabel('Période')
                    plt.ylabel('Productivité (unités/heure)')
                    plt.grid(True, linestyle='--', alpha=0.7)
                    plt.xticks(rotation=45)
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    graphiques['productivite'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
                # Graphique de performance des lignes
                if kpis['performance_lignes']:
                    plt.figure(figsize=(12, 6))
                    
                    lignes = [item['nom'] for item in kpis['performance_lignes']]
                    performances = [item['performance'] for item in kpis['performance_lignes']]
                    
                    plt.barh(lignes, performances, color='green')
                    plt.title('Performance des lignes de production')
                    plt.xlabel('Performance (unités/heure)')
                    plt.ylabel('Ligne de production')
                    plt.grid(True, linestyle='--', alpha=0.7)
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    graphiques['performance_lignes'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
                # KPI combiné: Taux de conformité qualité
                cursor.execute(f"""
                    SELECT {groupe_date} as periode,
                           COUNT(*) as total,
                           SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) as conformes,
                           ROUND(SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) / COUNT(*) * 100, 2) as taux
                    FROM controles_qualite
                    WHERE date_controle BETWEEN %s AND %s
                    GROUP BY periode
                    ORDER BY periode
                """, (f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"))
                evolution_qualite = cursor.fetchall()
                
                if evolution_qualite:
                    plt.figure(figsize=(12, 6))
                    
                    periodes = [item['periode'] for item in evolution_qualite]
                    taux = [item['taux'] for item in evolution_qualite]
                    
                    plt.plot(periodes, taux, 'g-', marker='o')
                    plt.axhline(y=95, color='r', linestyle='--', label='Objectif (95%)')
                    plt.title(f'Évolution du taux de conformité ({periode_texte})')
                    plt.xlabel('Période')
                    plt.ylabel('Taux de conformité (%)')
                    plt.legend()
                    plt.grid(True, linestyle='--', alpha=0.7)
                    plt.xticks(rotation=45)
                    plt.tight_layout()
                    
                    buffer = io.BytesIO()
                    plt.savefig(buffer, format='png')
                    buffer.seek(0)
                    graphiques['qualite'] = base64.b64encode(buffer.getvalue()).decode('utf-8')
                    plt.close()
                
        except Exception as e:
            flash(f'Erreur lors de la génération du tableau de bord KPI: {str(e)}', 'danger')
            logger.error(f"Erreur rapport KPI: {str(e)}")
        finally:
            conn.close()
    
    return render_template('rapports/kpi.html', 
                          kpis=kpis, 
                          graphiques=graphiques,
                          periode=periode,
                          periode_texte=periode_texte,
                          date_debut=date_debut,
                          date_fin=date_fin)

@app.route('/rapports/alertes')
@login_required
@role_required('supervisor')
@log_activity('rapport_alertes')
def rapport_alertes():
    """Rapport sur les alertes et notifications du système."""
    conn = get_db_connection()
    alertes = {
        'stock': [],
        'qualite': [],
        'maintenance': [],
        'production': []
    }
    
    # Initialiser evolution_data et stats comme une liste et un dict vides
    evolution_data = []
    stats = {
        'critiques': 0,
        'hautes': 0,
        'moyennes': 0,
        'basses': 0,
        'resolues': 0,
        'nouvelles': 0,
        'en_cours': 0,
        'ignorees': 0,
        'production': 0,
        'maintenance': 0,
        'qualite': 0,
        'stock': 0,
        'securite': 0
    }
    
    # Variable pour le template
    utilisateurs = []
    config = {
        'alerte_rendement': True,
        'seuil_rendement': 80,
        'alerte_rebut': True,
        'seuil_rebut': 5,
        'alerte_arret': True,
        'duree_arret': 30,
        'alerte_panne': True,
        'alerte_maintenance_preventive': True,
        'delai_maintenance': 7,
        'alerte_temperature': True,
        'seuil_temperature': 50,
        'alerte_non_conformite': True,
        'seuil_non_conformite': 5,
        'alerte_reclamation': True,
        'alerte_controle_qualite': True,
        'alerte_stock_min': True,
        'alerte_rupture': True,
        'alerte_peremption': True,
        'delai_peremption': 30,
        'alerte_accident': True,
        'alerte_incident': True,
        'alerte_formation_securite': True,
        'delai_formation_securite': 15,
        'notif_application': True,
        'notif_email': True,
        'notif_sms': False,
        'destinataires_notif': [1, 2],
        'frequence_recap': 'quotidien'
    }
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Obtenir la liste des utilisateurs pour les assignations
                cursor.execute("""
                    SELECT id, prenom, nom FROM utilisateurs
                    WHERE actif = 1 AND role IN ('supervisor', 'manager', 'operator')
                    ORDER BY nom, prenom
                """)
                utilisateurs = cursor.fetchall()
                
                # Alertes de stock (produits sous le seuil d'alerte)
                cursor.execute("""
                    SELECT s.*, p.nom as produit_nom, p.reference, p.categorie, e.nom as entrepot_nom,
                           (s.quantite / s.seuil_alerte) * 100 as pourcentage_seuil
                    FROM stocks s
                    JOIN produits p ON s.produit_id = p.id
                    JOIN entrepots e ON s.entrepot_id = e.id
                    WHERE s.actif = 1 AND p.actif = 1 AND s.quantite <= s.seuil_alerte
                    ORDER BY pourcentage_seuil ASC
                """)
                alertes['stock'] = cursor.fetchall()
                
                # Comptage pour les statistiques
                stats['stock'] = len(alertes['stock'])
                for alerte in alertes['stock']:
                    if alerte['pourcentage_seuil'] < 25:
                        stats['critiques'] += 1
                    elif alerte['pourcentage_seuil'] < 50:
                        stats['hautes'] += 1
                    elif alerte['pourcentage_seuil'] < 75:
                        stats['moyennes'] += 1
                    else:
                        stats['basses'] += 1
                
                # Alertes de qualité (contrôles non conformes récents)
                cursor.execute("""
                    SELECT c.*, p.nom as produit_nom, p.reference, 
                           u.prenom, u.nom as nom_utilisateur
                    FROM controles_qualite c
                    JOIN produits p ON c.produit_id = p.id
                    JOIN utilisateurs u ON c.utilisateur_id = u.id
                    WHERE c.resultat = 'non_conforme'
                    AND c.date_controle >= DATE_SUB(NOW(), INTERVAL 30 DAY)
                    ORDER BY c.date_controle DESC
                """)
                alertes['qualite'] = cursor.fetchall()
                stats['qualite'] = len(alertes['qualite'])
                stats['hautes'] += len(alertes['qualite'])
                
                # Alertes de maintenance (maintenances en retard)
                cursor.execute("""
                    SELECT m.*, e.nom as equipement_nom, t.nom as type_nom,
                           DATEDIFF(NOW(), m.date_programmee) as jours_retard
                    FROM maintenance m
                    JOIN equipements e ON m.equipement_id = e.id
                    JOIN types_maintenance t ON m.type_maintenance_id = t.id
                    WHERE m.statut = 'planifie' AND m.date_programmee < CURDATE()
                    ORDER BY m.date_programmee
                """)
                alertes['maintenance'] = cursor.fetchall()
                stats['maintenance'] = len(alertes['maintenance'])
                
                # Catégoriser par priorité
                for alerte in alertes['maintenance']:
                    if alerte['jours_retard'] > 7:
                        stats['critiques'] += 1
                    elif alerte['jours_retard'] > 3:
                        stats['hautes'] += 1
                    else:
                        stats['moyennes'] += 1
                
                # Alertes de production (écart significatif par rapport aux moyennes)
                cursor.execute("""
                    SELECT p.*, pr.nom as produit_nom, pr.reference, l.nom as ligne_nom,
                           (SELECT AVG(quantite_produite / temps_production) 
                            FROM production 
                            WHERE produit_id = p.produit_id AND ligne_production_id = p.ligne_production_id
                            AND id != p.id AND temps_production > 0) as productivite_moyenne,
                           (p.quantite_produite / p.temps_production) as productivite_actuelle
                    FROM production p
                    JOIN produits pr ON p.produit_id = pr.id
                    JOIN lignes_production l ON p.ligne_production_id = l.id
                    WHERE p.date_creation >= DATE_SUB(NOW(), INTERVAL 30 DAY)
                    AND p.temps_production > 0
                    HAVING productivite_moyenne IS NOT NULL 
                    AND ABS(productivite_actuelle - productivite_moyenne) / productivite_moyenne > 0.30  -- Écart de plus de 30%
                    ORDER BY p.date_creation DESC
                """)
                alertes['production'] = cursor.fetchall()
                stats['production'] = len(alertes['production'])
                stats['moyennes'] += len(alertes['production'])
                
                # Évolution des alertes (derniers 30 jours)
                try:
                    cursor.execute("""
                        SELECT DATE_FORMAT(date_creation, '%Y-%m-%d') as jour,
                               COUNT(*) as nouvelles_alertes
                        FROM logs_alertes
                        WHERE date_creation >= DATE_SUB(NOW(), INTERVAL 30 DAY)
                        GROUP BY jour
                        ORDER BY jour
                    """)
                    evolution_data = cursor.fetchall()
                except Exception as e:
                    # En cas d'erreur sur cette requête spécifique (table inexistante par exemple)
                    logger.warning(f"Impossible de récupérer l'évolution des alertes: {str(e)}")
                    evolution_data = []
                
                # Ajouter des statistiques basées sur le statut des alertes
                # Ces valeurs seraient normalement issues d'une table d'alertes
                stats['nouvelles'] = stats['critiques'] + (stats['hautes'] // 2)
                stats['en_cours'] = (stats['hautes'] // 2) + (stats['moyennes'] // 2)
                stats['resolues'] = 12  # Valeur exemple
                stats['ignorees'] = 3   # Valeur exemple
                stats['securite'] = 5   # Valeur exemple
                
        except Exception as e:
            flash(f'Erreur lors de la génération du rapport d\'alertes: {str(e)}', 'danger')
            logger.error(f"Erreur rapport alertes: {str(e)}")
        finally:
            conn.close()
    
    # Prepare evolution data for chart
    evolution_labels = []
    evolution_nouvelles = []
    evolution_resolues = []
    
    if evolution_data:
        for item in evolution_data:
            evolution_labels.append(item['jour'])
            evolution_nouvelles.append(item['nouvelles_alertes'])
            # Pour les alertes résolues, vous auriez besoin d'une autre requête ou d'ajuster votre modèle de données
            evolution_resolues.append(0)  # Valeur par défaut
    else:
        # Données d'exemple si aucune donnée n'est disponible
        today = datetime.now()
        for i in range(7):
            day = today - timedelta(days=i)
            evolution_labels.append(day.strftime('%Y-%m-%d'))
            evolution_nouvelles.append(random.randint(0, 5))
            evolution_resolues.append(random.randint(0, 4))
        evolution_labels.reverse()
        evolution_nouvelles.reverse()
        evolution_resolues.reverse()
    
    return render_template('rapports/alertes.html', 
                          alertes=alertes,
                          evolution_labels=evolution_labels,
                          evolution_nouvelles=evolution_nouvelles,
                          evolution_resolues=evolution_resolues,
                          stats=stats,
                          utilisateurs=utilisateurs,
                          config=config)

@app.template_filter('format_datetime')
def format_datetime(value, format='%d/%m/%Y %H:%M'):
    """Format a datetime object to a string."""
    if value is None:
        return ""
    if isinstance(value, str):
        try:
            value = datetime.strptime(value, '%Y-%m-%d %H:%M:%S')
        except ValueError:
            try:
                value = datetime.strptime(value, '%Y-%m-%d')
            except ValueError:
                return value
    return value.strftime(format)

@app.template_filter('format_date')
def format_date(value, format='%d/%m/%Y'):
    """Format a date object to a string."""
    if value is None:
        return ""
    if isinstance(value, str):
        try:
            value = datetime.strptime(value, '%Y-%m-%d')
        except ValueError:
            return value
    return value.strftime(format)

@app.route('/export/<rapport_type>')
@login_required
@role_required('supervisor')
@log_activity('export_rapport')
def export_data(rapport_type):
    """Export des données au format Excel."""
    conn = get_db_connection()
    df = None
    
    # Paramètres par défaut
    date_debut = request.args.get('date_debut', (datetime.now() - timedelta(days=30)).strftime('%Y-%m-%d'))
    date_fin = request.args.get('date_fin', datetime.now().strftime('%Y-%m-%d'))
    
    if conn:
        try:
            with conn.cursor() as cursor:
                if rapport_type == 'production':
                    sql = """
                    SELECT p.*, pr.nom as produit_nom, pr.reference, pr.categorie, 
                           l.nom as ligne_nom,
                           u.prenom, u.nom as nom_utilisateur
                    FROM production p
                    JOIN produits pr ON p.produit_id = pr.id
                    JOIN lignes_production l ON p.ligne_production_id = l.id
                    JOIN utilisateurs u ON p.utilisateur_id = u.id
                    WHERE p.date_creation BETWEEN %s AND %s
                    ORDER BY p.date_creation DESC
                    """
                    cursor.execute(sql, (f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"))
                    data = cursor.fetchall()
                    
                    if data:
                        df = pd.DataFrame(data)
                        # Renommer et réorganiser les colonnes pour l'export
                        columns = {
                            'id': 'ID',
                            'produit_id': 'ID Produit',
                            'produit_nom': 'Produit',
                            'reference': 'Référence',
                            'categorie': 'Catégorie',
                            'ligne_production_id': 'ID Ligne',
                            'ligne_nom': 'Ligne de production',
                            'quantite_produite': 'Quantité produite',
                            'temps_production': 'Temps (h)',
                            'numero_lot': 'Numéro de lot',
                            'commentaire': 'Commentaire',
                            'date_creation': 'Date',
                            'prenom': 'Prénom Utilisateur',
                            'nom_utilisateur': 'Nom Utilisateur'
                        }
                        df = df.rename(columns=columns)
                        # Ajouter colonne Productivité
                        df['Productivité (unités/h)'] = df['Quantité produite'] / df['Temps (h)']
                
                elif rapport_type == 'qualite':
                    sql = """
                    SELECT c.*, p.nom as produit_nom, p.reference, p.categorie,
                           u.prenom, u.nom as nom_utilisateur
                    FROM controles_qualite c
                    JOIN produits p ON c.produit_id = p.id
                    JOIN utilisateurs u ON c.utilisateur_id = u.id
                    WHERE c.date_controle BETWEEN %s AND %s
                    ORDER BY c.date_controle DESC
                    """
                    cursor.execute(sql, (f"{date_debut} 00:00:00", f"{date_fin} 23:59:59"))
                    data = cursor.fetchall()
                    
                    if data:
                        df = pd.DataFrame(data)
                        # Renommer les colonnes
                        columns = {
                            'id': 'ID',
                            'produit_id': 'ID Produit',
                            'produit_nom': 'Produit',
                            'reference': 'Référence',
                            'categorie': 'Catégorie',
                            'lot_id': 'ID Lot',
                            'numero_lot': 'Numéro de lot',
                            'numero_serie': 'Numéro de série',
                            'type_controle': 'Type de contrôle',
                            'resultat': 'Résultat',
                            'commentaire': 'Commentaire',
                            'date_controle': 'Date du contrôle',
                            'prenom': 'Prénom Utilisateur',
                            'nom_utilisateur': 'Nom Utilisateur'
                        }
                        df = df.rename(columns=columns)
                        # Formater les résultats
                        df['Résultat'] = df['Résultat'].apply(lambda x: 'Conforme' if x == 'conforme' else 'Non conforme' if x == 'non_conforme' else 'En attente')
                
                elif rapport_type == 'stocks':
                    sql = """
                    SELECT s.*, p.nom as produit_nom, p.reference, p.categorie, 
                           e.nom as entrepot_nom
                    FROM stocks s
                    JOIN produits p ON s.produit_id = p.id
                    JOIN entrepots e ON s.entrepot_id = e.id
                    WHERE s.actif = 1 AND p.actif = 1
                    ORDER BY p.nom, e.nom
                    """
                    cursor.execute(sql)
                    data = cursor.fetchall()
                    
                    if data:
                        df = pd.DataFrame(data)
                        # Renommer les colonnes
                        columns = {
                            'id': 'ID',
                            'produit_id': 'ID Produit',
                            'produit_nom': 'Produit',
                            'reference': 'Référence',
                            'categorie': 'Catégorie',
                            'entrepot_id': 'ID Entrepôt',
                            'entrepot_nom': 'Entrepôt',
                            'quantite': 'Quantité en stock',
                            'seuil_alerte': 'Seuil d\'alerte',
                            'date_creation': 'Date de création',
                            'date_modification': 'Dernière modification'
                        }
                        df = df.rename(columns=columns)
                        # Ajouter statut de stock
                        df['Statut'] = df.apply(lambda row: 'Rupture' if row['Quantité en stock'] == 0 
                                               else 'Critique' if row['Quantité en stock'] <= row['Seuil d\'alerte'] / 2
                                               else 'Alerte' if row['Quantité en stock'] <= row['Seuil d\'alerte']
                                               else 'Normal', axis=1)
                        # Ajouter pourcentage du seuil
                        df['% du seuil'] = (df['Quantité en stock'] / df['Seuil d\'alerte'] * 100).round(2)
                
                elif rapport_type == 'maintenance':
                    sql = """
                    SELECT m.*, e.nom as equipement_nom, e.numero_serie,
                           l.nom as ligne_nom,
                           t.nom as type_nom,
                           u.prenom, u.nom as nom_utilisateur
                    FROM maintenance m
                    JOIN equipements e ON m.equipement_id = e.id
                    LEFT JOIN lignes_production l ON e.ligne_production_id = l.id
                    JOIN types_maintenance t ON m.type_maintenance_id = t.id
                    JOIN utilisateurs u ON m.utilisateur_id = u.id
                    WHERE m.date_programmee BETWEEN %s AND %s
                    ORDER BY m.date_programmee DESC
                    """
                    cursor.execute(sql, (date_debut, date_fin))
                    data = cursor.fetchall()
                    
                    if data:
                        df = pd.DataFrame(data)
                        # Renommer les colonnes
                        columns = {
                            'id': 'ID',
                            'equipement_id': 'ID Équipement',
                            'equipement_nom': 'Équipement',
                            'numero_serie': 'N° Série',
                            'ligne_nom': 'Ligne de production',
                            'type_maintenance_id': 'ID Type',
                            'type_nom': 'Type de maintenance',
                            'date_programmee': 'Date programmée',
                            'date_fin': 'Date de fin',
                            'duree_estimee': 'Durée estimée (h)',
                            'description': 'Description',
                            'statut': 'Statut',
                            'priorite': 'Priorité',
                            'impact_production': 'Impact production',
                            'prenom': 'Prénom Utilisateur',
                            'nom_utilisateur': 'Nom Utilisateur'
                        }
                        df = df.rename(columns=columns)
                        # Formater les statuts
                        statut_map = {
                            'planifie': 'Planifiée',
                            'en_cours': 'En cours',
                            'terminee': 'Terminée',
                            'annulee': 'Annulée'
                        }
                        df['Statut'] = df['Statut'].map(statut_map)
                        # Formater les priorités
                        priorite_map = {
                            'haute': 'Haute',
                            'moyenne': 'Moyenne',
                            'basse': 'Basse'
                        }
                        df['Priorité'] = df['Priorité'].map(priorite_map)
                
                elif rapport_type == 'kpi':
                    # Créer un rapport KPI combiné
                    
                    # 1. KPI de production
                    cursor.execute("""
                        SELECT DATE_FORMAT(date_creation, '%Y-%m') as mois,
                               SUM(quantite_produite) as quantite_totale,
                               COUNT(*) as nb_productions,
                               ROUND(AVG(quantite_produite / temps_production), 2) as productivite_moyenne
                        FROM production
                        WHERE date_creation >= DATE_SUB(NOW(), INTERVAL 12 MONTH)
                        AND temps_production > 0
                        GROUP BY mois
                        ORDER BY mois
                    """)
                    production_kpi = cursor.fetchall()
                    
                    # 2. KPI de qualité
                    cursor.execute("""
                        SELECT DATE_FORMAT(date_controle, '%Y-%m') as mois,
                               COUNT(*) as nb_controles,
                               SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) as nb_conformes,
                               ROUND(SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) / COUNT(*) * 100, 2) as taux_conformite
                        FROM controles_qualite
                        WHERE date_controle >= DATE_SUB(NOW(), INTERVAL 12 MONTH)
                        GROUP BY mois
                        ORDER BY mois
                    """)
                    qualite_kpi = cursor.fetchall()
                    
                    # 3. KPI de maintenance
                    cursor.execute("""
                        SELECT DATE_FORMAT(date_programmee, '%Y-%m') as mois,
                               COUNT(*) as nb_maintenances,
                               SUM(CASE WHEN statut = 'terminee' THEN 1 ELSE 0 END) as nb_terminees,
                               ROUND(AVG(CASE WHEN statut = 'terminee' AND date_fin IS NOT NULL 
                                     THEN TIMESTAMPDIFF(HOUR, date_programmee, date_fin) 
                                     ELSE NULL END), 2) as temps_moyen_resolution
                        FROM maintenance
                        WHERE date_programmee >= DATE_SUB(NOW(), INTERVAL 12 MONTH)
                        GROUP BY mois
                        ORDER BY mois
                    """)
                    maintenance_kpi = cursor.fetchall()
                    
                    # Créer les dataframes
                    df_prod = pd.DataFrame(production_kpi)
                    df_qual = pd.DataFrame(qualite_kpi)
                    df_maint = pd.DataFrame(maintenance_kpi)
                    
                    # Fusionner les dataframes sur la colonne 'mois'
                    if not df_prod.empty and not df_qual.empty:
                        df = pd.merge(df_prod, df_qual, on='mois', how='outer')
                        if not df_maint.empty:
                            df = pd.merge(df, df_maint, on='mois', how='outer')
                    elif not df_prod.empty:
                        df = df_prod
                    elif not df_qual.empty:
                        df = df_qual
                    else:
                        df = df_maint if not df_maint.empty else None
                    
                    if df is not None:
                        # Renommer les colonnes
                        columns = {
                            'mois': 'Mois',
                            'quantite_totale': 'Production totale',
                            'nb_productions': 'Nb de productions',
                            'productivite_moyenne': 'Productivité moyenne',
                            'nb_controles': 'Nb de contrôles qualité',
                            'nb_conformes': 'Nb conformes',
                            'taux_conformite': 'Taux de conformité (%)',
                            'nb_maintenances': 'Nb de maintenances',
                            'nb_terminees': 'Nb maintenances terminées',
                            'temps_moyen_resolution': 'Temps moyen résolution (h)'
                        }
                        df = df.rename(columns=columns)
                
        except Exception as e:
            flash(f'Erreur lors de l\'export: {str(e)}', 'danger')
            logger.error(f"Erreur export {rapport_type}: {str(e)}")
        finally:
            conn.close()
    
    if df is not None:
        # Créer un buffer pour stocker le fichier Excel
        output = io.BytesIO()
        
        # Créer le fichier Excel
        with pd.ExcelWriter(output, engine='xlsxwriter') as writer:
            df.to_excel(writer, sheet_name=rapport_type.capitalize(), index=False)
            
            # Formater le document Excel
            workbook = writer.book
            worksheet = writer.sheets[rapport_type.capitalize()]
            
            # Format pour les en-têtes
            header_format = workbook.add_format({
                'bold': True,
                'text_wrap': True,
                'valign': 'top',
                'fg_color': '#D7E4BC',
                'border': 1
            })
            
            # Format pour les nombres
            number_format = workbook.add_format({
                'num_format': '# ##0',
                'align': 'right'
            })
            
            # Format pour les pourcentages
            percent_format = workbook.add_format({
                'num_format': '0.00%',
                'align': 'right'
            })
            
            # Format pour les dates
            date_format = workbook.add_format({
                'num_format': 'dd/mm/yyyy hh:mm',
                'align': 'center'
            })
            
            # Appliquer le format d'en-tête
            for col_num, value in enumerate(df.columns.values):
                worksheet.write(0, col_num, value, header_format)
                
            # Déterminer le format de chaque colonne
            for i, col in enumerate(df.columns):
                # Ajuster la largeur des colonnes
                column_width = max(df[col].astype(str).map(len).max(), len(col)) + 2
                worksheet.set_column(i, i, column_width)
                
                # Appliquer des formats spécifiques selon le type de données
                if 'Date' in col:
                    worksheet.set_column(i, i, column_width, date_format)
                elif 'Quantité' in col or 'Nb' in col or 'total' in col:
                    worksheet.set_column(i, i, column_width, number_format)
                elif '%' in col or 'Taux' in col or 'Pourcentage' in col:
                    worksheet.set_column(i, i, column_width, percent_format)
            
            # Ajouter une table avec filtres
            table_options = {
                'columns': [{'header': col} for col in df.columns],
                'style': 'Table Style Medium 2',
                'first_column': False,
                'header_row': True,
                'autofilter': True
            }
            worksheet.add_table(0, 0, len(df), len(df.columns) - 1, table_options)
        
        # Préparer le fichier pour le téléchargement
        output.seek(0)
        
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        filename = generate_report_name("rapport", rapport_type, date_debut, date_fin)
        
        return send_file(
            output,
            as_attachment=True,
            download_name=f"{filename}.xlsx",
            mimetype='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet'
        )
    
    flash('Aucune donnée disponible pour l\'export', 'warning')
    return redirect(url_for('rapports_liste'))

# =============================================================================
# GESTION DES PARAMÈTRES ET ADMINISTRATION
# =============================================================================


@app.route('/parametres/utilisateurs')
@login_required
@role_required('manager')
@log_activity('liste_utilisateurs')
def parametres_utilisateurs():
    """Gestion des utilisateurs du système."""
    conn = get_db_connection()
    utilisateurs = []
    
    # Ajouter des données pour les graphiques
    stats = {
        'admin': 2,
        'manager': 3,
        'production': 8,
        'qualite': 4,
        'maintenance': 5,
        'logistique': 3
    }
    
    # Données pour le graphique d'activité
    activity_labels = []
    activity_data = []
    
    # Générer des données de test pour le graphique d'activité
    today = datetime.now()
    for i in range(7):
        day = today - timedelta(days=i)
        activity_labels.append(day.strftime('%Y-%m-%d'))
        activity_data.append(random.randint(1, 10))  # Nombre aléatoire de connexions
    
    # Inverser les listes pour avoir l'ordre chronologique
    activity_labels.reverse()
    activity_data.reverse()
    
    if conn:
        try:
            with conn.cursor() as cursor:
                sql = """
                SELECT id, nom, prenom, nom_utilisateur, email, role, actif, 
                       date_creation, derniere_connexion
                FROM utilisateurs 
                ORDER BY nom, prenom
                """
                cursor.execute(sql)
                utilisateurs = cursor.fetchall()
                
                # Formater pour l'affichage
                for user in utilisateurs:
                    # Définir la classe pour le statut actif/inactif
                    user['statut'] = 'actif' if user['actif'] else 'inactif'
                    
                    # Formater le rôle pour l'affichage
                    if user['role'] == 'admin':
                        user['role_affichage'] = 'Administrateur'
                        user['classe_role'] = 'danger'
                    elif user['role'] == 'manager':
                        user['role_affichage'] = 'Manager'
                        user['classe_role'] = 'warning'
                    elif user['role'] == 'supervisor':
                        user['role_affichage'] = 'Superviseur'
                        user['classe_role'] = 'primary'
                    elif user['role'] == 'operator':
                        user['role_affichage'] = 'Opérateur'
                        user['classe_role'] = 'info'
                    else:
                        user['role_affichage'] = 'Utilisateur'
                        user['classe_role'] = 'secondary'
                    
                    # Ajouter le département (fictif si non présent)
                    user['departement_nom'] = 'Général'  # Par défaut
                
                # Si pas d'utilisateurs, ajouter des exemples pour le développement
                if not utilisateurs and app.debug:
                    utilisateurs = [
                        {'id': 1, 'nom': 'Admin', 'prenom': 'System', 'nom_utilisateur': 'admin', 
                         'email': 'admin@example.com', 'role': 'admin', 'role_affichage': 'Administrateur', 
                         'classe_role': 'danger', 'statut': 'actif', 'departement_nom': 'Direction',
                         'date_creation': datetime.now() - timedelta(days=365), 
                         'derniere_connexion': datetime.now()},
                        {'id': 2, 'nom': 'Manager', 'prenom': 'Production', 'nom_utilisateur': 'manager', 
                         'email': 'manager@example.com', 'role': 'manager', 'role_affichage': 'Manager', 
                         'classe_role': 'warning', 'statut': 'actif', 'departement_nom': 'Production',
                         'date_creation': datetime.now() - timedelta(days=180), 
                         'derniere_connexion': datetime.now() - timedelta(days=2)},
                    ]
        except Exception as e:
            flash(f'Erreur lors de la récupération des utilisateurs: {str(e)}', 'danger')
            logger.error(f"Erreur liste utilisateurs: {str(e)}")
        finally:
            conn.close()
    
    # Liste des départements pour le filtre
    departements = [
        {'id': 1, 'nom': 'Direction'},
        {'id': 2, 'nom': 'Production'},
        {'id': 3, 'nom': 'Qualité'},
        {'id': 4, 'nom': 'Maintenance'},
        {'id': 5, 'nom': 'Logistique'}
    ]
    
    return render_template('parametres/utilisateurs.html', 
                          utilisateurs=utilisateurs,
                          stats=stats,
                          activity_labels=activity_labels,
                          activity_data=activity_data,
                          departements=departements)


@app.route('/parametres/utilisateurs/ajouter', methods=['GET', 'POST'])
@login_required
@role_required('manager')
@log_activity('ajout_utilisateur')
def parametres_utilisateur_ajouter():
    """Ajout d'un nouvel utilisateur."""
    if request.method == 'POST':
        nom = request.form.get('nom')
        prenom = request.form.get('prenom')
        nom_utilisateur = request.form.get('nom_utilisateur')
        email = request.form.get('email')
        mot_de_passe = request.form.get('mot_de_passe')
        confirmation = request.form.get('confirmation')
        role = request.form.get('role')
        
        # Validation
        if not all([nom, prenom, nom_utilisateur, email, mot_de_passe, confirmation, role]):
            flash('Tous les champs sont obligatoires', 'danger')
            return render_template('parametres/utilisateur_ajouter.html')
        
        if mot_de_passe != confirmation:
            flash('Les mots de passe ne correspondent pas', 'danger')
            return render_template('parametres/utilisateur_ajouter.html')
        
        # Vérifier la complexité du mot de passe
        if len(mot_de_passe) < 8:
            flash('Le mot de passe doit contenir au moins 8 caractères', 'danger')
            return render_template('parametres/utilisateur_ajouter.html')
        
        conn = get_db_connection()
        if conn:
            try:
                # Vérifier si le nom d'utilisateur existe déjà
                with conn.cursor() as cursor:
                    cursor.execute("SELECT id FROM utilisateurs WHERE nom_utilisateur = %s", (nom_utilisateur,))
                    existing_user = cursor.fetchone()
                    
                    if existing_user:
                        flash('Ce nom d\'utilisateur existe déjà', 'danger')
                        return render_template('parametres/utilisateur_ajouter.html')
                    
                    # Vérifier si l'email existe déjà
                    cursor.execute("SELECT id FROM utilisateurs WHERE email = %s", (email,))
                    existing_email = cursor.fetchone()
                    
                    if existing_email:
                        flash('Cet email existe déjà', 'danger')
                        return render_template('parametres/utilisateur_ajouter.html')
                    
                    # Hacher le mot de passe
                    hashed_password = generate_password_hash(mot_de_passe)
                    
                    # Insérer le nouvel utilisateur
                    sql = """
                    INSERT INTO utilisateurs 
                    (nom, prenom, nom_utilisateur, email, mot_de_passe, role, actif, date_creation)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                    """
                    cursor.execute(sql, (nom, prenom, nom_utilisateur, email, hashed_password, role, 1, datetime.now()))
                    conn.commit()
                    
                    # Vérifier si c'est un utilisateur admin et qu'il faut envoyer un email
                    if role in ['admin', 'manager'] and request.form.get('envoyer_email') == 'on':
                        sujet = "Vos identifiants de connexion - ManufacturingSoft Algérie"
                        corps = f"""
                        Bonjour {prenom} {nom},
                        
                        Votre compte a été créé sur le système ManufacturingSoft Algérie.
                        
                        Vos identifiants de connexion sont:
                        - Nom d'utilisateur: {nom_utilisateur}
                        - Mot de passe: (celui que vous avez défini)
                        
                        Veuillez vous connecter à l'adresse suivante et changer votre mot de passe après la première connexion:
                        {request.host_url}
                        
                        Cordialement,
                        L'équipe ManufacturingSoft
                        """
                        
                        send_notification_email(sujet, [email], corps)
                    
                    flash('Utilisateur ajouté avec succès', 'success')
                    logger.info(f"Utilisateur ajouté: {nom_utilisateur}")
                    return redirect(url_for('parametres_utilisateurs'))
            except Exception as e:
                flash(f'Erreur lors de l\'ajout de l\'utilisateur: {str(e)}', 'danger')
                logger.error(f"Erreur ajout utilisateur: {str(e)}")
            finally:
                conn.close()
    
    return render_template('parametres/utilisateur_ajouter.html')

@app.route('/parametres')
@login_required
@role_required('manager')
@log_activity('menu_parametres')
def parametres():
    """Menu principal des paramètres du système."""
    
    # Liste des routes disponibles dans l'application
    available_routes = {
        'parametres_utilisateurs': True,  # Cette route existe certainement
        'parametres_lignes_production': True,  # Cette route existe probablement
        'parametres_entrepots': True,  # Cette route existe probablement
        'parametres_equipements': True,  # Cette route existe probablement
        'parametres_types_maintenance': True,  # Cette route existe probablement
        'parametres_categories_produits': True,  # Cette route existe probablement
        'parametres_normes': True,  # Cette route existe probablement
        'parametres_database': True,  # Cette route existe probablement
        'parametres_systeme': True  # Cette route existe probablement
    }
    
    # Vérification des routes qui pourraient ne pas exister
    # Pour chaque route potentiellement manquante, vérifiez si elle existe dans l'application
    potential_routes = [
        'parametres_fournisseurs',
        'parametres_clients',
        'parametres_unite_mesure',
        'parametres_devises',
        'parametres_taxes',
        'parametres_documents',
        'parametres_workflow',
        'parametres_notifications',
        'parametres_api',
        'parametres_backup'
    ]
    
    # Vérifiez l'existence de chaque route potentielle
    for route in potential_routes:
        try:
            url_for(route)
            available_routes[route] = True
        except:
            available_routes[route] = False
    
    return render_template('parametres/index.html', available_routes=available_routes)

@app.route('/parametres/fournisseurs')
@login_required
@role_required('manager')
@log_activity('liste_fournisseurs')
def parametres_fournisseurs():
    """Gestion des fournisseurs."""
    # Créez une page temporaire
    flash("La gestion des fournisseurs n'est pas encore implémentée dans cette version.", "info")
    
    fournisseurs = []  # Liste vide par défaut
    
    # Vous pouvez ajouter des données de test pour le développement
    if app.debug:
        fournisseurs = [
            {'id': 1, 'nom': 'Fournisseur Test 1', 'telephone': '0123456789', 'email': 'contact@fournisseur1.dz', 'ville': 'Alger', 'statut': 'actif'},
            {'id': 2, 'nom': 'Fournisseur Test 2', 'telephone': '0123456780', 'email': 'contact@fournisseur2.dz', 'ville': 'Oran', 'statut': 'actif'},
        ]
    
    return render_template('parametres/fournisseurs.html', fournisseurs=fournisseurs)


@app.route('/parametres/utilisateurs/<int:utilisateur_id>', methods=['GET', 'POST'])
@login_required
@role_required('manager')
@log_activity('modification_utilisateur')
@audit_trail('utilisateurs')
def parametres_utilisateur_modifier(utilisateur_id):
    """Modification d'un utilisateur existant."""
    conn = get_db_connection()
    utilisateur = None
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer l'utilisateur
                cursor.execute("SELECT * FROM utilisateurs WHERE id = %s", (utilisateur_id,))
                utilisateur = cursor.fetchone()
                
                if not utilisateur:
                    flash('Utilisateur non trouvé', 'warning')
                    return redirect(url_for('parametres_utilisateurs'))
                
                # Vérifier que l'on ne modifie pas un utilisateur de niveau supérieur
                current_role = session.get('role')
                if not has_permission('admin') and utilisateur['role'] in ['admin', 'manager'] and utilisateur['id'] != session.get('user_id'):
                    flash('Vous n\'avez pas les droits pour modifier cet utilisateur', 'danger')
                    return redirect(url_for('parametres_utilisateurs'))
                
                if request.method == 'POST':
                    nom = request.form.get('nom')
                    prenom = request.form.get('prenom')
                    email = request.form.get('email')
                    role = request.form.get('role')
                    actif = request.form.get('actif') == 'on'
                    changer_mdp = request.form.get('changer_mdp') == 'on'
                    
                    # Vérifier si l'email existe déjà pour un autre utilisateur
                    cursor.execute("SELECT id FROM utilisateurs WHERE email = %s AND id != %s", (email, utilisateur_id))
                    existing_email = cursor.fetchone()
                    
                    if existing_email:
                        flash('Cet email existe déjà pour un autre utilisateur', 'danger')
                    else:
                        # Mise à jour des informations de base
                        sql = """
                        UPDATE utilisateurs 
                        SET nom = %s, prenom = %s, email = %s, role = %s, actif = %s, date_modification = %s
                        WHERE id = %s
                        """
                        cursor.execute(sql, (nom, prenom, email, role, actif, datetime.now(), utilisateur_id))
                        
                        # Si demande de changement de mot de passe
                        if changer_mdp:
                            nouveau_mdp = request.form.get('nouveau_mdp')
                            confirmation = request.form.get('confirmation')
                            
                            if not nouveau_mdp or nouveau_mdp != confirmation:
                                flash('Les mots de passe ne correspondent pas', 'danger')
                            elif len(nouveau_mdp) < 8:
                                flash('Le mot de passe doit contenir au moins 8 caractères', 'danger')
                            else:
                                # Hacher et mettre à jour le mot de passe
                                hashed_password = generate_password_hash(nouveau_mdp)
                                cursor.execute("""
                                    UPDATE utilisateurs 
                                    SET mot_de_passe = %s, tentatives_echec = 0
                                    WHERE id = %s
                                """, (hashed_password, utilisateur_id))
                                
                                flash('Mot de passe mis à jour', 'success')
                                
                                # Envoyer un email de notification si l'option est cochée
                                if request.form.get('notifier') == 'on':
                                    sujet = "Votre mot de passe a été réinitialisé - ManufacturingSoft Algérie"
                                    corps = f"""
                                    Bonjour {prenom} {nom},
                                    
                                    Votre mot de passe a été réinitialisé sur le système ManufacturingSoft Algérie.
                                    
                                    Vous pouvez vous connecter avec votre nouveau mot de passe à l'adresse suivante:
                                    {request.host_url}
                                    
                                    Si vous n'êtes pas à l'origine de cette demande, veuillez contacter immédiatement votre administrateur.
                                    
                                    Cordialement,
                                    L'équipe ManufacturingSoft
                                    """
                                    
                                    send_notification_email(sujet, [email], corps)
                        
                        conn.commit()
                        flash('Utilisateur modifié avec succès', 'success')
                        logger.info(f"Utilisateur modifié: ID {utilisateur_id}")
                        return redirect(url_for('parametres_utilisateurs'))
        except Exception as e:
            flash(f'Erreur lors de la modification de l\'utilisateur: {str(e)}', 'danger')
            logger.error(f"Erreur modification utilisateur {utilisateur_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('parametres/utilisateur_modifier.html', utilisateur=utilisateur)

@app.route('/parametres/utilisateurs/<int:utilisateur_id>/supprimer', methods=['POST'])
@login_required
@role_required('admin')
@log_activity('suppression_utilisateur')
def parametres_utilisateur_supprimer(utilisateur_id):
    """Suppression d'un utilisateur."""
    conn = get_db_connection()
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Vérifier si l'utilisateur existe
                cursor.execute("SELECT * FROM utilisateurs WHERE id = %s", (utilisateur_id,))
                utilisateur = cursor.fetchone()
                
                if not utilisateur:
                    flash('Utilisateur non trouvé', 'warning')
                    return redirect(url_for('parametres_utilisateurs'))
                
                # Vérifier qu'on ne supprime pas un admin si on n'est pas admin
                if utilisateur['role'] == 'admin' and not has_permission('admin'):
                    flash('Vous n\'avez pas les droits pour supprimer cet administrateur', 'danger')
                    return redirect(url_for('parametres_utilisateurs'))
                
                # Vérifier qu'on ne se supprime pas soi-même
                if utilisateur_id == session.get('user_id'):
                    flash('Vous ne pouvez pas supprimer votre propre compte', 'danger')
                    return redirect(url_for('parametres_utilisateurs'))
                
                # Vérifier s'il y a des dépendances actives
                cursor.execute("""
                    SELECT COUNT(*) as total 
                    FROM (
                        SELECT utilisateur_id FROM production WHERE utilisateur_id = %s
                        UNION
                        SELECT utilisateur_id FROM mouvements_stock WHERE utilisateur_id = %s
                        UNION
                        SELECT utilisateur_id FROM controles_qualite WHERE utilisateur_id = %s
                        UNION
                        SELECT utilisateur_id FROM maintenance WHERE utilisateur_id = %s
                    ) as dependencies
                """, (utilisateur_id, utilisateur_id, utilisateur_id, utilisateur_id))
                
                dependencies = cursor.fetchone()['total']
                
                if dependencies > 0:
                    # Désactiver l'utilisateur au lieu de le supprimer
                    cursor.execute("""
                        UPDATE utilisateurs
                        SET actif = 0, date_modification = %s
                        WHERE id = %s
                    """, (datetime.now(), utilisateur_id))
                    flash('Utilisateur désactivé car il possède des données associées', 'warning')
                else:
                    # Supprimer l'utilisateur
                    cursor.execute("DELETE FROM utilisateurs WHERE id = %s", (utilisateur_id,))
                    flash('Utilisateur supprimé avec succès', 'success')
                
                conn.commit()
                logger.info(f"Utilisateur {'désactivé' if dependencies > 0 else 'supprimé'}: ID {utilisateur_id}")
                return redirect(url_for('parametres_utilisateurs'))
                
        except Exception as e:
            flash(f'Erreur lors de la suppression de l\'utilisateur: {str(e)}', 'danger')
            logger.error(f"Erreur suppression utilisateur {utilisateur_id}: {str(e)}")
        finally:
            conn.close()
    
    return redirect(url_for('parametres_utilisateurs'))

@app.route('/parametres/lignes-production')
@login_required
@role_required('supervisor')
@log_activity('liste_lignes_parametres')
def parametres_lignes_production():
    """Gestion des lignes de production."""
    conn = get_db_connection()
    lignes = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                sql = "SELECT * FROM lignes_production ORDER BY nom"
                cursor.execute(sql)
                lignes = cursor.fetchall()
        except Exception as e:
            flash(f'Erreur lors de la récupération des lignes de production: {str(e)}', 'danger')
            logger.error(f"Erreur liste lignes: {str(e)}")
        finally:
            conn.close()
    
    return render_template('parametres/lignes_production.html', lignes=lignes)

@app.route('/parametres/lignes-production/ajouter', methods=['GET', 'POST'])
@login_required
@role_required('manager')
@log_activity('ajout_ligne_production')
def parametres_ligne_production_ajouter():
    """Ajout d'une ligne de production."""
    if request.method == 'POST':
        nom = request.form.get('nom')
        description = request.form.get('description')
        capacite = request.form.get('capacite')
        statut = request.form.get('statut')
        emplacement = request.form.get('emplacement')
        date_installation = request.form.get('date_installation')
        responsable = request.form.get('responsable')
        
        conn = get_db_connection()
        if conn:
            try:
                with conn.cursor() as cursor:
                    # Vérifier si le nom existe déjà
                    cursor.execute("SELECT id FROM lignes_production WHERE nom = %s", (nom,))
                    if cursor.fetchone():
                        flash('Une ligne de production avec ce nom existe déjà', 'danger')
                        return render_template('parametres/ligne_production_ajouter.html')
                    
                    sql = """
                    INSERT INTO lignes_production 
                    (nom, description, capacite, statut, emplacement, date_installation, 
                     responsable, utilisateur_id, date_creation)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                    """
                    cursor.execute(sql, (
                        nom, description, capacite, statut, emplacement, date_installation, 
                        responsable, session['user_id'], datetime.now()
                    ))
                    conn.commit()
                    
                    flash('Ligne de production ajoutée avec succès', 'success')
                    logger.info(f"Ligne production ajoutée: {nom}")
                    return redirect(url_for('parametres_lignes_production'))
            except Exception as e:
                flash(f'Erreur lors de l\'ajout de la ligne de production: {str(e)}', 'danger')
                logger.error(f"Erreur ajout ligne: {str(e)}")
            finally:
                conn.close()
    
    return render_template('parametres/ligne_production_ajouter.html')

@app.route('/parametres/lignes-production/<int:ligne_id>', methods=['GET', 'POST'])
@login_required
@role_required('supervisor')
@log_activity('modification_ligne_production')
@audit_trail('lignes_production')
def parametres_ligne_production_modifier(ligne_id):
    """Modification d'une ligne de production."""
    conn = get_db_connection()
    ligne = None
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer la ligne
                cursor.execute("SELECT * FROM lignes_production WHERE id = %s", (ligne_id,))
                ligne = cursor.fetchone()
                
                if not ligne:
                    flash('Ligne de production non trouvée', 'warning')
                    return redirect(url_for('parametres_lignes_production'))
                
                if request.method == 'POST':
                    nom = request.form.get('nom')
                    description = request.form.get('description')
                    capacite = request.form.get('capacite')
                    statut = request.form.get('statut')
                    emplacement = request.form.get('emplacement')
                    date_installation = request.form.get('date_installation')
                    responsable = request.form.get('responsable')
                    actif = request.form.get('actif') == 'on'
                    
                    # Vérifier si le nom existe déjà pour une autre ligne
                    cursor.execute("SELECT id FROM lignes_production WHERE nom = %s AND id != %s", (nom, ligne_id))
                    if cursor.fetchone():
                        flash('Une autre ligne de production avec ce nom existe déjà', 'danger')
                    else:
                        # Mise à jour de la ligne
                        sql = """
                        UPDATE lignes_production 
                        SET nom = %s, description = %s, capacite = %s, statut = %s, 
                            emplacement = %s, date_installation = %s, responsable = %s, 
                            actif = %s, date_modification = %s
                        WHERE id = %s
                        """
                        cursor.execute(sql, (
                            nom, description, capacite, statut, 
                            emplacement, date_installation, responsable, 
                            actif, datetime.now(), ligne_id
                        ))
                        conn.commit()
                        
                        flash('Ligne de production modifiée avec succès', 'success')
                        logger.info(f"Ligne production modifiée: ID {ligne_id}")
                        return redirect(url_for('parametres_lignes_production'))
        except Exception as e:
            flash(f'Erreur lors de la modification de la ligne de production: {str(e)}', 'danger')
            logger.error(f"Erreur modification ligne {ligne_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('parametres/ligne_production_modifier.html', ligne=ligne)

@app.route('/parametres/entrepots')
@login_required
@role_required('supervisor')
@log_activity('liste_entrepots')
def parametres_entrepots():
    """Gestion des entrepôts."""
    conn = get_db_connection()
    entrepots = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                sql = """
                SELECT e.*, u.prenom, u.nom as nom_utilisateur,
                      (SELECT SUM(s.quantite) FROM stocks s WHERE s.entrepot_id = e.id AND s.actif = 1) as total_stock,
                      (SELECT COUNT(DISTINCT s.produit_id) FROM stocks s WHERE s.entrepot_id = e.id AND s.actif = 1) as nb_produits
                FROM entrepots e
                LEFT JOIN utilisateurs u ON e.utilisateur_id = u.id
                ORDER BY e.nom
                """
                cursor.execute(sql)
                entrepots = cursor.fetchall()
        except Exception as e:
            flash(f'Erreur lors de la récupération des entrepôts: {str(e)}', 'danger')
            logger.error(f"Erreur liste entrepôts: {str(e)}")
        finally:
            conn.close()
    
    return render_template('parametres/entrepots.html', entrepots=entrepots)

@app.route('/parametres/entrepots/ajouter', methods=['GET', 'POST'])
@login_required
@role_required('manager')
@log_activity('ajout_entrepot')
def parametres_entrepot_ajouter():
    """Ajout d'un entrepôt."""
    if request.method == 'POST':
        nom = request.form.get('nom')
        adresse = request.form.get('adresse')
        ville = request.form.get('ville')
        code_postal = request.form.get('code_postal')
        capacite = request.form.get('capacite')
        responsable = request.form.get('responsable')
        est_production = request.form.get('est_production') == 'on'
        
        conn = get_db_connection()
        if conn:
            try:
                with conn.cursor() as cursor:
                    # Vérifier si le nom existe déjà
                    cursor.execute("SELECT id FROM entrepots WHERE nom = %s", (nom,))
                    if cursor.fetchone():
                        flash('Un entrepôt avec ce nom existe déjà', 'danger')
                        return render_template('parametres/entrepot_ajouter.html')
                    
                    sql = """
                    INSERT INTO entrepots 
                    (nom, adresse, ville, code_postal, capacite, responsable, 
                     est_production, utilisateur_id, date_creation)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                    """
                    cursor.execute(sql, (
                        nom, adresse, ville, code_postal, capacite, responsable, 
                        est_production, session['user_id'], datetime.now()
                    ))
                    conn.commit()
                    
                    flash('Entrepôt ajouté avec succès', 'success')
                    logger.info(f"Entrepôt ajouté: {nom}")
                    return redirect(url_for('parametres_entrepots'))
            except Exception as e:
                flash(f'Erreur lors de l\'ajout de l\'entrepôt: {str(e)}', 'danger')
                logger.error(f"Erreur ajout entrepôt: {str(e)}")
            finally:
                conn.close()
    
    return render_template('parametres/entrepot_ajouter.html')

@app.route('/parametres/entrepots/<int:entrepot_id>', methods=['GET', 'POST'])
@login_required
@role_required('supervisor')
@log_activity('modification_entrepot')
@audit_trail('entrepots')
def parametres_entrepot_modifier(entrepot_id):
    """Modification d'un entrepôt."""
    conn = get_db_connection()
    entrepot = None
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer l'entrepôt
                cursor.execute("SELECT * FROM entrepots WHERE id = %s", (entrepot_id,))
                entrepot = cursor.fetchone()
                
                if not entrepot:
                    flash('Entrepôt non trouvé', 'warning')
                    return redirect(url_for('parametres_entrepots'))
                
                if request.method == 'POST':
                    nom = request.form.get('nom')
                    adresse = request.form.get('adresse')
                    ville = request.form.get('ville')
                    code_postal = request.form.get('code_postal')
                    capacite = request.form.get('capacite')
                    responsable = request.form.get('responsable')
                    est_production = request.form.get('est_production') == 'on'
                    actif = request.form.get('actif') == 'on'
                    
                    # Vérifier si le nom existe déjà pour un autre entrepôt
                    cursor.execute("SELECT id FROM entrepots WHERE nom = %s AND id != %s", (nom, entrepot_id))
                    if cursor.fetchone():
                        flash('Un autre entrepôt avec ce nom existe déjà', 'danger')
                    else:
                        # Mise à jour de l'entrepôt
                        sql = """
                        UPDATE entrepots 
                        SET nom = %s, adresse = %s, ville = %s, code_postal = %s, 
                            capacite = %s, responsable = %s, est_production = %s, 
                            actif = %s, date_modification = %s
                        WHERE id = %s
                        """
                        cursor.execute(sql, (
                            nom, adresse, ville, code_postal, 
                            capacite, responsable, est_production, 
                            actif, datetime.now(), entrepot_id
                        ))
                        conn.commit()
                        
                        flash('Entrepôt modifié avec succès', 'success')
                        logger.info(f"Entrepôt modifié: ID {entrepot_id}")
                        return redirect(url_for('parametres_entrepots'))
        except Exception as e:
            flash(f'Erreur lors de la modification de l\'entrepôt: {str(e)}', 'danger')
            logger.error(f"Erreur modification entrepôt {entrepot_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('parametres/entrepot_modifier.html', entrepot=entrepot)

@app.route('/parametres/equipements')
@login_required
@role_required('supervisor')
@log_activity('liste_equipements_parametres')
def parametres_equipements():
    """Gestion des équipements."""
    conn = get_db_connection()
    equipements = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                sql = """
                SELECT e.*, l.nom as ligne_nom 
                FROM equipements e
                LEFT JOIN lignes_production l ON e.ligne_production_id = l.id
                ORDER BY e.nom
                """
                cursor.execute(sql)
                equipements = cursor.fetchall()
        except Exception as e:
            flash(f'Erreur lors de la récupération des équipements: {str(e)}', 'danger')
            logger.error(f"Erreur liste équipements: {str(e)}")
        finally:
            conn.close()
    
    return render_template('parametres/equipements.html', equipements=equipements)

@app.route('/parametres/equipements/ajouter', methods=['GET', 'POST'])
@login_required
@role_required('supervisor')
@log_activity('ajout_equipement')
def parametres_equipement_ajouter():
    """Ajout d'un équipement."""
    conn = get_db_connection()
    lignes = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Liste des lignes de production
                cursor.execute("SELECT id, nom FROM lignes_production WHERE actif = 1 ORDER BY nom")
                lignes = cursor.fetchall()
                
                if request.method == 'POST':
                    nom = request.form.get('nom')
                    numero_serie = request.form.get('numero_serie')
                    fabricant = request.form.get('fabricant')
                    modele = request.form.get('modele')
                    date_acquisition = request.form.get('date_acquisition')
                    date_mise_service = request.form.get('date_mise_service')
                    ligne_production_id = request.form.get('ligne_production_id') or None
                    statut = request.form.get('statut')
                    description = request.form.get('description')
                    
                    # Vérifier si le numéro de série existe déjà
                    if numero_serie:
                        cursor.execute("SELECT id FROM equipements WHERE numero_serie = %s", (numero_serie,))
                        if cursor.fetchone():
                            flash('Un équipement avec ce numéro de série existe déjà', 'danger')
                            return render_template('parametres/equipement_ajouter.html', lignes=lignes)
                    
                    # Enregistrer l'équipement
                    sql = """
                    INSERT INTO equipements 
                    (nom, numero_serie, fabricant, modele, date_acquisition, date_mise_service,
                     ligne_production_id, statut, description, utilisateur_id, date_creation)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                    """
                    cursor.execute(sql, (
                        nom, numero_serie, fabricant, modele, date_acquisition, date_mise_service, 
                        ligne_production_id, statut, description, session['user_id'], datetime.now()
                    ))
                    conn.commit()
                    
                    flash('Équipement ajouté avec succès', 'success')
                    logger.info(f"Équipement ajouté: {nom}")
                    return redirect(url_for('parametres_equipements'))
        except Exception as e:
            flash(f'Erreur lors de l\'ajout de l\'équipement: {str(e)}', 'danger')
            logger.error(f"Erreur ajout équipement: {str(e)}")
        finally:
            conn.close()
    
    return render_template('parametres/equipement_ajouter.html', lignes=lignes)

@app.route('/parametres/equipements/<int:equipement_id>', methods=['GET', 'POST'])
@login_required
@role_required('supervisor')
@log_activity('modification_equipement')
@audit_trail('equipements')
def parametres_equipement_modifier(equipement_id):
    """Modification d'un équipement."""
    conn = get_db_connection()
    equipement = None
    lignes = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Liste des lignes de production
                cursor.execute("SELECT id, nom FROM lignes_production WHERE actif = 1 ORDER BY nom")
                lignes = cursor.fetchall()
                
                # Récupérer l'équipement
                cursor.execute("SELECT * FROM equipements WHERE id = %s", (equipement_id,))
                equipement = cursor.fetchone()
                
                if not equipement:
                    flash('Équipement non trouvé', 'warning')
                    return redirect(url_for('parametres_equipements'))
                
                if request.method == 'POST':
                    nom = request.form.get('nom')
                    numero_serie = request.form.get('numero_serie')
                    fabricant = request.form.get('fabricant')
                    modele = request.form.get('modele')
                    date_acquisition = request.form.get('date_acquisition')
                    date_mise_service = request.form.get('date_mise_service')
                    ligne_production_id = request.form.get('ligne_production_id') or None
                    statut = request.form.get('statut')
                    description = request.form.get('description')
                    actif = request.form.get('actif') == 'on'
                    
                    # Vérifier si le numéro de série existe déjà pour un autre équipement
                    if numero_serie:
                        cursor.execute("SELECT id FROM equipements WHERE numero_serie = %s AND id != %s", (numero_serie, equipement_id))
                        if cursor.fetchone():
                            flash('Un autre équipement avec ce numéro de série existe déjà', 'danger')
                            return render_template('parametres/equipement_modifier.html', 
                                                  equipement=equipement, lignes=lignes)
                    
                    # Mise à jour de l'équipement
                    sql = """
                    UPDATE equipements 
                    SET nom = %s, numero_serie = %s, fabricant = %s, modele = %s,
                        date_acquisition = %s, date_mise_service = %s, ligne_production_id = %s,
                        statut = %s, description = %s, actif = %s, date_modification = %s
                    WHERE id = %s
                    """
                    cursor.execute(sql, (
                        nom, numero_serie, fabricant, modele, 
                        date_acquisition, date_mise_service, ligne_production_id,
                        statut, description, actif, datetime.now(), equipement_id
                    ))
                    conn.commit()
                    
                    flash('Équipement modifié avec succès', 'success')
                    logger.info(f"Équipement modifié: ID {equipement_id}")
                    return redirect(url_for('parametres_equipements'))
        except Exception as e:
            flash(f'Erreur lors de la modification de l\'équipement: {str(e)}', 'danger')
            logger.error(f"Erreur modification équipement {equipement_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('parametres/equipement_modifier.html', equipement=equipement, lignes=lignes)

@app.route('/parametres/types-maintenance')
@login_required
@role_required('supervisor')
@log_activity('liste_types_maintenance')
def parametres_types_maintenance():
    """Gestion des types de maintenance."""
    conn = get_db_connection()
    types = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                sql = """
                SELECT t.*, u.prenom, u.nom as nom_utilisateur,
                       (SELECT COUNT(*) FROM maintenance WHERE type_maintenance_id = t.id) as nb_maintenances
                FROM types_maintenance t
                LEFT JOIN utilisateurs u ON t.utilisateur_id = u.id
                ORDER BY t.nom
                """
                cursor.execute(sql)
                types = cursor.fetchall()
        except Exception as e:
            flash(f'Erreur lors de la récupération des types de maintenance: {str(e)}', 'danger')
            logger.error(f"Erreur liste types maintenance: {str(e)}")
        finally:
            conn.close()
    
    return render_template('parametres/types_maintenance.html', types=types)

@app.route('/parametres/types-maintenance/ajouter', methods=['GET', 'POST'])
@login_required
@role_required('supervisor')
@log_activity('ajout_type_maintenance')
def parametres_type_maintenance_ajouter():
    """Ajout d'un type de maintenance."""
    if request.method == 'POST':
        nom = request.form.get('nom')
        description = request.form.get('description')
        frequence = request.form.get('frequence')
        duree_standard = request.form.get('duree_standard')
        impact_production = request.form.get('impact_production') == 'on'
        procedure = request.form.get('procedure')
        
        conn = get_db_connection()
        if conn:
            try:
                with conn.cursor() as cursor:
                    # Vérifier si le nom existe déjà
                    cursor.execute("SELECT id FROM types_maintenance WHERE nom = %s", (nom,))
                    if cursor.fetchone():
                        flash('Un type de maintenance avec ce nom existe déjà', 'danger')
                        return render_template('parametres/type_maintenance_ajouter.html')
                    
                    sql = """
                    INSERT INTO types_maintenance 
                    (nom, description, frequence, duree_standard, impact_production, procedure,
                     utilisateur_id, date_creation)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                    """
                    cursor.execute(sql, (
                        nom, description, frequence, duree_standard, impact_production, procedure,
                        session['user_id'], datetime.now()
                    ))
                    conn.commit()
                    
                    flash('Type de maintenance ajouté avec succès', 'success')
                    logger.info(f"Type maintenance ajouté: {nom}")
                    return redirect(url_for('parametres_types_maintenance'))
            except Exception as e:
                flash(f'Erreur lors de l\'ajout du type de maintenance: {str(e)}', 'danger')
                logger.error(f"Erreur ajout type maintenance: {str(e)}")
            finally:
                conn.close()
    
    return render_template('parametres/type_maintenance_ajouter.html')

@app.route('/parametres/types-maintenance/<int:type_id>', methods=['GET', 'POST'])
@login_required
@role_required('supervisor')
@log_activity('modification_type_maintenance')
@audit_trail('types_maintenance')
def parametres_type_maintenance_modifier(type_id):
    """Modification d'un type de maintenance."""
    conn = get_db_connection()
    type_maintenance = None
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer le type de maintenance
                cursor.execute("SELECT * FROM types_maintenance WHERE id = %s", (type_id,))
                type_maintenance = cursor.fetchone()
                
                if not type_maintenance:
                    flash('Type de maintenance non trouvé', 'warning')
                    return redirect(url_for('parametres_types_maintenance'))
                
                if request.method == 'POST':
                    nom = request.form.get('nom')
                    description = request.form.get('description')
                    frequence = request.form.get('frequence')
                    duree_standard = request.form.get('duree_standard')
                    impact_production = request.form.get('impact_production') == 'on'
                    procedure = request.form.get('procedure')
                    actif = request.form.get('actif') == 'on'
                    
                    # Vérifier si le nom existe déjà pour un autre type
                    cursor.execute("SELECT id FROM types_maintenance WHERE nom = %s AND id != %s", (nom, type_id))
                    if cursor.fetchone():
                        flash('Un autre type de maintenance avec ce nom existe déjà', 'danger')
                    else:
                        # Mise à jour du type
                        sql = """
                        UPDATE types_maintenance 
                        SET nom = %s, description = %s, frequence = %s, duree_standard = %s,
                            impact_production = %s, procedure = %s, actif = %s, date_modification = %s
                        WHERE id = %s
                        """
                        cursor.execute(sql, (
                            nom, description, frequence, duree_standard, 
                            impact_production, procedure, actif, datetime.now(), type_id
                        ))
                        conn.commit()
                        
                        flash('Type de maintenance modifié avec succès', 'success')
                        logger.info(f"Type maintenance modifié: ID {type_id}")
                        return redirect(url_for('parametres_types_maintenance'))
        except Exception as e:
            flash(f'Erreur lors de la modification du type de maintenance: {str(e)}', 'danger')
            logger.error(f"Erreur modification type maintenance {type_id}: {str(e)}")
        finally:
            conn.close()
    
    return render_template('parametres/type_maintenance_modifier.html', type_maintenance=type_maintenance)

@app.route('/parametres/categories-produits')
@login_required
@role_required('supervisor')
@log_activity('liste_categories_produits')
def parametres_categories_produits():
    """Gestion des catégories de produits."""
    conn = get_db_connection()
    categories = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Récupérer les catégories avec statistiques
                sql = """
                SELECT categorie, 
                       COUNT(*) as nb_produits,
                       AVG(prix_unitaire) as prix_moyen
                FROM produits
                WHERE actif = 1
                GROUP BY categorie
                ORDER BY categorie
                """
                cursor.execute(sql)
                categories = cursor.fetchall()
        except Exception as e:
            flash(f'Erreur lors de la récupération des catégories: {str(e)}', 'danger')
            logger.error(f"Erreur liste catégories: {str(e)}")
        finally:
            conn.close()
    
    return render_template('parametres/categories_produits.html', categories=categories)

@app.route('/parametres/normes')
@login_required
@role_required('supervisor')
@log_activity('liste_normes_parametres')
def parametres_normes():
    """Gestion des normes de qualité."""
    conn = get_db_connection()
    normes = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                sql = """
                SELECT n.*, u.prenom, u.nom as nom_utilisateur,
                       (SELECT COUNT(*) FROM normes_produits WHERE norme_id = n.id) as nb_produits
                FROM normes n
                LEFT JOIN utilisateurs u ON n.utilisateur_id = u.id
                ORDER BY n.categorie, n.code
                """
                cursor.execute(sql)
                normes = cursor.fetchall()
        except Exception as e:
            flash(f'Erreur lors de la récupération des normes: {str(e)}', 'danger')
            logger.error(f"Erreur liste normes paramètres: {str(e)}")
        finally:
            conn.close()
    
    return render_template('parametres/normes.html', normes=normes)

@app.route('/parametres/normes/ajouter', methods=['GET', 'POST'])
@login_required
@role_required('supervisor')
@log_activity('ajout_norme')
def parametres_norme_ajouter():
    """Ajout d'une norme de qualité."""
    if request.method == 'POST':
        code = request.form.get('code')
        nom = request.form.get('nom')
        description = request.form.get('description')
        categorie = request.form.get('categorie')
        organisme = request.form.get('organisme')
        date_publication = request.form.get('date_publication')
        
        conn = get_db_connection()
        if conn:
            try:
                with conn.cursor() as cursor:
                    # Vérifier si le code existe déjà
                    cursor.execute("SELECT id FROM normes WHERE code = %s", (code,))
                    if cursor.fetchone():
                        flash('Une norme avec ce code existe déjà', 'danger')
                        return render_template('parametres/norme_ajouter.html')
                    
                    # Gérer le téléchargement d'un document si présent
                    document_url = None
                    if 'document' in request.files:
                        document_file = request.files['document']
                        if document_file and document_file.filename != '' and allowed_file(document_file.filename):
                            secure_name = sanitize_filename(document_file.filename)
                            unique_filename = generate_unique_filename(secure_name)
                            
                            document_dir = os.path.join(app.config['UPLOAD_FOLDER'], 'normes')
                            os.makedirs(document_dir, exist_ok=True)
                            
                            filepath = os.path.join(document_dir, unique_filename)
                            document_file.save(filepath)
                            document_url = f"/static/uploads/normes/{unique_filename}"
                    
                    sql = """
                    INSERT INTO normes 
                    (code, nom, description, categorie, organisme, date_publication,
                     document_url, utilisateur_id, date_creation)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                    """
                    cursor.execute(sql, (
                        code, nom, description, categorie, organisme, date_publication,
                        document_url, session['user_id'], datetime.now()
                    ))
                    conn.commit()
                    
                    flash('Norme ajoutée avec succès', 'success')
                    logger.info(f"Norme ajoutée: {code} - {nom}")
                    return redirect(url_for('parametres_normes'))
            except Exception as e:
                flash(f'Erreur lors de l\'ajout de la norme: {str(e)}', 'danger')
                logger.error(f"Erreur ajout norme: {str(e)}")
            finally:
                conn.close()
    
    return render_template('parametres/norme_ajouter.html')

@app.route('/parametres/database')
@login_required
@role_required('admin')
@log_activity('status_database')
def parametres_database():
    """Affichage du statut de la base de données."""
    conn = get_db_connection()
    stats = {}
    tables = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Informations générales sur la base de données
                cursor.execute("SHOW TABLE STATUS")
                tables_info = cursor.fetchall()
                
                # Calculer la taille totale
                total_size = sum(table['Data_length'] + table['Index_length'] for table in tables_info)
                stats['total_size'] = round(total_size / (1024 * 1024), 2)  # En MB
                stats['nb_tables'] = len(tables_info)
                
                # Informations sur les tables
                for table in tables_info:
                    size = round((table['Data_length'] + table['Index_length']) / (1024 * 1024), 2)  # En MB
                    
                    # Compter le nombre d'enregistrements
                    cursor.execute(f"SELECT COUNT(*) as count FROM {table['Name']}")
                    count = cursor.fetchone()['count']
                    
                    tables.append({
                        'name': table['Name'],
                        'rows': table['Rows'],
                        'size': size,
                        'count': count,
                        'engine': table['Engine'],
                        'created': table['Create_time'],
                        'updated': table['Update_time']
                    })
                
                # Statistiques supplémentaires
                cursor.execute("SELECT COUNT(*) as count FROM utilisateurs WHERE actif = 1")
                stats['users_active'] = cursor.fetchone()['count']
                
                cursor.execute("SELECT COUNT(*) as count FROM produits WHERE actif = 1")
                stats['products_active'] = cursor.fetchone()['count']
                
                cursor.execute("SELECT SUM(quantite) as total FROM stocks WHERE actif = 1")
                stats['stock_total'] = cursor.fetchone()['total'] or 0
                
                cursor.execute("SELECT COUNT(*) as count FROM production")
                stats['productions'] = cursor.fetchone()['count']
                
                cursor.execute("SELECT COUNT(*) as count FROM controles_qualite")
                stats['quality_controls'] = cursor.fetchone()['count']
                
                cursor.execute("SELECT COUNT(*) as count FROM maintenance")
                stats['maintenances'] = cursor.fetchone()['count']
                
                # Dernière sauvegarde
                cursor.execute("SELECT date_creation FROM backups ORDER BY date_creation DESC LIMIT 1")
                last_backup = cursor.fetchone()
                stats['last_backup'] = last_backup['date_creation'] if last_backup else None
                
        except Exception as e:
            flash(f'Erreur lors de la récupération des informations de la base de données: {str(e)}', 'danger')
            logger.error(f"Erreur status base de données: {str(e)}")
        finally:
            conn.close()
    
    return render_template('parametres/database.html', stats=stats, tables=tables)

@app.route('/parametres/database/backup', methods=['POST'])
@login_required
@role_required('admin')
@log_activity('backup_database')
def parametres_database_backup():
    """Création d'une sauvegarde de la base de données."""
    try:
        # Créer le répertoire de sauvegarde s'il n'existe pas
        backup_dir = os.path.join(app.root_path, 'backups')
        os.makedirs(backup_dir, exist_ok=True)
        
        # Générer un nom de fichier unique avec timestamp
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        backup_filename = f"backup_{db_config['database']}_{timestamp}.sql"
        backup_path = os.path.join(backup_dir, backup_filename)
        
        # Commande pour mysqldump
        mysqldump_cmd = [
            'mysqldump',
            '--user=' + db_config['user'],
            f"--host={db_config['host']}",
            '--single-transaction',
            '--routines',
            '--triggers',
            '--databases', db_config['database']
        ]
        
        # Ajouter le mot de passe si présent
        if db_config['password']:
            mysqldump_cmd.append('--password=' + db_config['password'])
        
        # Exécuter la commande et rediriger vers le fichier
        with open(backup_path, 'w') as f:
            result = subprocess.run(mysqldump_cmd, stdout=f, stderr=subprocess.PIPE, text=True)
        
        if result.returncode != 0:
            raise Exception(f"Erreur mysqldump: {result.stderr}")
        
        # Compresser le fichier
        with open(backup_path, 'rb') as f_in:
            with gzip.open(backup_path + '.gz', 'wb') as f_out:
                f_out.writelines(f_in)
        
        # Supprimer le fichier non compressé
        os.remove(backup_path)
        
        # Enregistrer l'information de sauvegarde dans la base de données
        conn = get_db_connection()
        if conn:
            try:
                with conn.cursor() as cursor:
                    cursor.execute("""
                        INSERT INTO backups (nom_fichier, chemin, taille, utilisateur_id, date_creation)
                        VALUES (%s, %s, %s, %s, %s)
                    """, (
                        backup_filename + '.gz',
                        f"backups/{backup_filename}.gz",
                        os.path.getsize(backup_path + '.gz'),
                        session['user_id'],
                        datetime.now()
                    ))
                    conn.commit()
            finally:
                conn.close()
        
        flash('Sauvegarde de la base de données créée avec succès', 'success')
        logger.info(f"Sauvegarde de la base de données créée: {backup_filename}.gz")
    except Exception as e:
        flash(f'Erreur lors de la sauvegarde de la base de données: {str(e)}', 'danger')
        logger.error(f"Erreur sauvegarde base de données: {str(e)}")
    
    return redirect(url_for('parametres_database'))

@app.route('/parametres/logs')
@login_required
@role_required('admin')
@log_activity('consultation_logs')
def parametres_logs():
    """Consultation des logs système."""
    log_type = request.args.get('type', 'system')
    page = request.args.get('page', 1, type=int)
    per_page = request.args.get('per_page', 100, type=int)
    
    logs = []
    pagination = {'page': page, 'per_page': per_page, 'total_count': 0, 'total_pages': 0}
    
    if log_type == 'system':
        # Logs système depuis le fichier
        log_file = os.path.join(LOG_FOLDER, 'production_app.log')
        if os.path.exists(log_file):
            with open(log_file, 'r') as f:
                all_logs = f.readlines()
                all_logs.reverse()  # Afficher les plus récents en premier
                
                total_count = len(all_logs)
                pagination['total_count'] = total_count
                pagination['total_pages'] = (total_count + per_page - 1) // per_page
                
                start = (page - 1) * per_page
                end = min(start + per_page, total_count)
                
                logs = all_logs[start:end]
    else:
        # Logs d'activité depuis la base de données
        conn = get_db_connection()
        if conn:
            try:
                with conn.cursor() as cursor:
                    # Compter le nombre total d'enregistrements
                    if log_type == 'activity':
                        cursor.execute("SELECT COUNT(*) as count FROM logs_activite")
                    elif log_type == 'auth':
                        cursor.execute("SELECT COUNT(*) as count FROM logs_connexion")
                    elif log_type == 'audit':
                        cursor.execute("SELECT COUNT(*) as count FROM audit_trail")
                    
                    total_count = cursor.fetchone()['count']
                    pagination['total_count'] = total_count
                    pagination['total_pages'] = (total_count + per_page - 1) // per_page
                    
                    # Récupérer les logs paginés
                    if log_type == 'activity':
                        sql = """
                        SELECT l.*, u.nom_utilisateur
                        FROM logs_activite l
                        LEFT JOIN utilisateurs u ON l.utilisateur_id = u.id
                        ORDER BY l.date_creation DESC
                        LIMIT %s OFFSET %s
                        """
                    elif log_type == 'auth':
                        sql = """
                        SELECT l.*, u.nom_utilisateur
                        FROM logs_connexion l
                        LEFT JOIN utilisateurs u ON l.utilisateur_id = u.id
                        ORDER BY l.date_creation DESC
                        LIMIT %s OFFSET %s
                        """
                    elif log_type == 'audit':
                        sql = """
                        SELECT a.*, u.nom_utilisateur
                        FROM audit_trail a
                        LEFT JOIN utilisateurs u ON a.utilisateur_id = u.id
                        ORDER BY a.date_creation DESC
                        LIMIT %s OFFSET %s
                        """
                    
                    cursor.execute(sql, (per_page, (page - 1) * per_page))
                    logs = cursor.fetchall()
            except Exception as e:
                flash(f'Erreur lors de la récupération des logs: {str(e)}', 'danger')
                logger.error(f"Erreur consultation logs: {str(e)}")
            finally:
                conn.close()
    
    return render_template('parametres/logs.html', 
                          logs=logs, 
                          log_type=log_type,
                          pagination=pagination)

@app.route('/parametres/systeme')
@login_required
@role_required('admin')
@log_activity('status_systeme')
def parametres_systeme():
    """Affichage des informations système."""
    system_info = {}
    
    # Informations sur le système d'exploitation
    system_info['os'] = platform.system()
    system_info['os_version'] = platform.version()
    system_info['architecture'] = platform.machine()
    system_info['processor'] = platform.processor()
    
    # Informations sur Python
    system_info['python_version'] = platform.python_version()
    system_info['python_implementation'] = platform.python_implementation()
    
    # Informations sur l'hôte
    system_info['hostname'] = socket.gethostname()
    try:
        system_info['ip'] = socket.gethostbyname(socket.gethostname())
    except:
        system_info['ip'] = '127.0.0.1'
    
    # Utilisation des ressources
    system_info['cpu_count'] = os.cpu_count()
    
    try:
        import psutil
        system_info['cpu_usage'] = psutil.cpu_percent(interval=1)
        system_info['memory_used'] = round(psutil.virtual_memory().used / (1024**3), 2)  # En GB
        system_info['memory_total'] = round(psutil.virtual_memory().total / (1024**3), 2)  # En GB
        system_info['memory_percent'] = psutil.virtual_memory().percent
        system_info['disk_used'] = round(psutil.disk_usage('/').used / (1024**3), 2)  # En GB
        system_info['disk_total'] = round(psutil.disk_usage('/').total / (1024**3), 2)  # En GB
        system_info['disk_percent'] = psutil.disk_usage('/').percent
    except ImportError:
        system_info['cpu_usage'] = 'N/A (psutil non disponible)'
        system_info['memory_used'] = 'N/A'
        system_info['memory_total'] = 'N/A'
        system_info['memory_percent'] = 'N/A'
        system_info['disk_used'] = 'N/A'
        system_info['disk_total'] = 'N/A'
        system_info['disk_percent'] = 'N/A'
    
    # Informations sur l'application
    system_info['app_start_time'] = datetime.fromtimestamp(
        psutil.Process(os.getpid()).create_time()
    ).strftime('%Y-%m-%d %H:%M:%S')
    
    system_info['app_version'] = '2.0.0'  # Version de l'application
    system_info['flask_version'] = version('flask')
    
    # Calcul du temps de fonctionnement
    start_time = psutil.Process(os.getpid()).create_time()
    uptime_seconds = time.time() - start_time
    days, remainder = divmod(uptime_seconds, 86400)
    hours, remainder = divmod(remainder, 3600)
    minutes, seconds = divmod(remainder, 60)
    system_info['uptime'] = f"{int(days)}j {int(hours)}h {int(minutes)}m {int(seconds)}s"
    
    return render_template('parametres/systeme.html', system_info=system_info)

# =============================================================================
# API INTERNE POUR AJAX
# =============================================================================

@app.route('/api/produits')
@login_required
def api_produits():
    """API pour récupérer la liste des produits."""
    conn = get_db_connection()
    produits = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                sql = "SELECT id, nom, reference FROM produits WHERE actif = 1 ORDER BY nom"
                cursor.execute(sql)
                produits = cursor.fetchall()
        except Exception as e:
            logger.error(f"Erreur API produits: {str(e)}")
        finally:
            conn.close()
    
    return jsonify(produits)

@app.route('/api/stocks')
@login_required
def api_stocks():
    """API pour récupérer les stocks d'un produit."""
    conn = get_db_connection()
    stocks = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                produit_id = request.args.get('produit_id')
                
                if produit_id:
                    sql = """
                    SELECT s.*, e.nom as entrepot_nom
                    FROM stocks s
                    JOIN entrepots e ON s.entrepot_id = e.id
                    WHERE s.produit_id = %s AND s.actif = 1
                    """
                    cursor.execute(sql, (produit_id,))
                else:
                    sql = """
                    SELECT s.*, p.nom as produit_nom, p.reference, e.nom as entrepot_nom
                    FROM stocks s
                    JOIN produits p ON s.produit_id = p.id
                    JOIN entrepots e ON s.entrepot_id = e.id
                    WHERE s.actif = 1 AND p.actif = 1
                    """
                    cursor.execute(sql)
                
                stocks = cursor.fetchall()
        except Exception as e:
            logger.error(f"Erreur API stocks: {str(e)}")
        finally:
            conn.close()
    
    return jsonify(stocks)

@app.route('/api/planning_disponibilite')
@login_required
def api_planning_disponibilite():
    """API pour vérifier la disponibilité d'une ligne de production."""
    conn = get_db_connection()
    planning = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                ligne_id = request.args.get('ligne_id')
                date = request.args.get('date')
                
                if ligne_id and date:
                    sql = """
                    SELECT id, date_production, heure_debut, heure_fin, produit_id, statut
                    FROM planning_production
                    WHERE ligne_production_id = %s AND date_production = %s
                    """
                    cursor.execute(sql, (ligne_id, date))
                    planning = cursor.fetchall()
        except Exception as e:
            logger.error(f"Erreur API planning: {str(e)}")
        finally:
            conn.close()
    
    return jsonify(planning)

@app.route('/api/stats_dashboard')
@login_required
def api_stats_dashboard():
    """API pour récupérer les statistiques du tableau de bord."""
    conn = get_db_connection()
    stats = {}
    
    if conn:
        try:
            with conn.cursor() as cursor:
                # Production des 7 derniers jours
                sql = """
                SELECT DATE(date_creation) as jour, SUM(quantite_produite) as total
                FROM production
                WHERE date_creation >= DATE_SUB(CURDATE(), INTERVAL 7 DAY)
                GROUP BY jour
                ORDER BY jour
                """
                cursor.execute(sql)
                production_semaine = cursor.fetchall()
                
                # Stock en alerte
                sql = """
                SELECT p.nom, p.reference, s.quantite, s.seuil_alerte, e.nom as entrepot_nom
                FROM stocks s
                JOIN produits p ON s.produit_id = p.id
                JOIN entrepots e ON s.entrepot_id = e.id
                WHERE s.quantite <= s.seuil_alerte AND s.actif = 1 AND p.actif = 1
                ORDER BY s.quantite / s.seuil_alerte
                LIMIT 5
                """
                cursor.execute(sql)
                stock_alerte = cursor.fetchall()
                
                # Maintenance planifiée à venir
                sql = """
                SELECT m.date_programmee, e.nom as equipement_nom, t.nom as type_nom, m.priorite
                FROM maintenance m
                JOIN equipements e ON m.equipement_id = e.id
                JOIN types_maintenance t ON m.type_maintenance_id = t.id
                WHERE m.statut = 'planifie' AND m.date_programmee >= CURDATE()
                ORDER BY m.date_programmee
                LIMIT 5
                """
                cursor.execute(sql)
                maintenance_planifiee = cursor.fetchall()
                
                # Taux de conformité qualité (30 derniers jours)
                sql = """
                SELECT 
                    COUNT(*) as total,
                    SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) as conformes,
                    ROUND(SUM(CASE WHEN resultat = 'conforme' THEN 1 ELSE 0 END) / COUNT(*) * 100, 2) as taux
                FROM controles_qualite
                WHERE date_controle >= DATE_SUB(CURDATE(), INTERVAL 30 DAY)
                """
                cursor.execute(sql)
                qualite = cursor.fetchone()
                
                stats = {
                    'production_semaine': production_semaine,
                    'stock_alerte': stock_alerte,
                    'maintenance_planifiee': maintenance_planifiee,
                    'qualite': qualite
                }
        except Exception as e:
            logger.error(f"Erreur API stats dashboard: {str(e)}")
        finally:
            conn.close()
    
    return jsonify(stats)

@app.route('/api/produit/<int:produit_id>/mouvements')
@login_required
def api_produit_mouvements(produit_id):
    """API pour récupérer les mouvements de stock d'un produit."""
    conn = get_db_connection()
    mouvements = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                sql = """
                SELECT m.*, e.nom as entrepot_nom 
                FROM mouvements_stock m
                JOIN entrepots e ON m.entrepot_id = e.id
                WHERE m.produit_id = %s
                ORDER BY m.date_mouvement DESC
                LIMIT 50
                """
                cursor.execute(sql, (produit_id,))
                mouvements = cursor.fetchall()
        except Exception as e:
            logger.error(f"Erreur API mouvements produit {produit_id}: {str(e)}")
        finally:
            conn.close()
    
    return jsonify(mouvements)

@app.route('/api/maintenance/disponibilite')
@login_required
def api_maintenance_disponibilite():
    """API pour vérifier la disponibilité d'un équipement pour maintenance."""
    conn = get_db_connection()
    maintenances = []
    
    if conn:
        try:
            with conn.cursor() as cursor:
                equipement_id = request.args.get('equipement_id')
                date = request.args.get('date')
                
                if equipement_id and date:
                    sql = """
                    SELECT * FROM maintenance
                    WHERE equipement_id = %s 
                    AND date_programmee = %s
                    AND statut IN ('planifie', 'en_cours')
                    """
                    cursor.execute(sql, (equipement_id, date))
                    maintenances = cursor.fetchall()
        except Exception as e:
            logger.error(f"Erreur API disponibilité maintenance: {str(e)}")
        finally:
            conn.close()
    
    return jsonify(maintenances)

# =============================================================================
# ROUTES D'ERREUR
# =============================================================================

@app.errorhandler(404)
def page_not_found(e):
    """Gestionnaire pour les erreurs 404 (Page non trouvée)."""
    logger.info(f"Page non trouvée: {request.path} - IP: {request.remote_addr}")
    return render_template('error.html', error_message="Page non trouvée", code=404), 404

@app.errorhandler(403)
def forbidden(e):
    """Gestionnaire pour les erreurs 403 (Accès refusé)."""
    logger.warning(f"Tentative d'accès non autorisé: {request.path} - IP: {request.remote_addr}")
    return render_template('error.html', error_message="Accès refusé", code=403), 403

@app.errorhandler(500)
def server_error(e):
    """Gestionnaire pour les erreurs 500 (Erreur interne du serveur)."""
    logger.error(f"Erreur serveur: {str(e)} - URL: {request.path} - IP: {request.remote_addr}")
    return render_template('error.html', 
                          error_message="Erreur interne du serveur. L'administrateur a été notifié.", 
                          code=500), 500

@app.errorhandler(429)
def too_many_requests(e):
    """Gestionnaire pour les erreurs 429 (Trop de requêtes)."""
    logger.warning(f"Trop de requêtes: {request.remote_addr} - {request.path}")
    return render_template('error.html', 
                          error_message="Trop de requêtes. Veuillez réessayer plus tard.", 
                          code=429), 429

# =============================================================================
# FONCTIONS UTILITAIRES AVANCÉES
# =============================================================================

def run_maintenance_check():
    """Vérification programmée des maintenances à venir et envoi de notifications."""
    with app.app_context():
        conn = get_db_connection()
        if conn:
            try:
                with conn.cursor() as cursor:
                    # Maintenances prévues pour demain
                    tomorrow = (datetime.now() + timedelta(days=1)).strftime('%Y-%m-%d')
                    sql = """
                    SELECT m.*, e.nom as equipement_nom, l.nom as ligne_nom, t.nom as type_nom
                    FROM maintenance m
                    JOIN equipements e ON m.equipement_id = e.id
                    LEFT JOIN lignes_production l ON e.ligne_production_id = l.id
                    JOIN types_maintenance t ON m.type_maintenance_id = t.id
                    WHERE m.date_programmee = %s AND m.statut = 'planifie'
                    """
                    cursor.execute(sql, (tomorrow,))
                    maintenances = cursor.fetchall()
                    
                    if maintenances:
                        # Récupérer les emails des managers et superviseurs
                        cursor.execute("""
                            SELECT email FROM utilisateurs 
                            WHERE role IN ('manager', 'supervisor') AND actif = 1
                        """)
                        emails = [row['email'] for row in cursor.fetchall()]
                        
                        if emails:
                            # Construire le message
                            sujet = f"Rappel: {len(maintenances)} maintenance(s) planifiée(s) pour demain"
                            
                            corps = f"""
                            Bonjour,
                            
                            Ce message est un rappel automatique concernant les maintenances planifiées pour demain ({tomorrow}).
                            
                            Maintenances prévues:
                            """
                            
                            for m in maintenances:
                                ligne_info = f" - Ligne: {m['ligne_nom']}" if m['ligne_nom'] else ""
                                corps += f"""
                                - Équipement: {m['equipement_nom']}{ligne_info}
                                  Type: {m['type_nom']}
                                  Priorité: {m['priorite']}
                                  Durée estimée: {m['duree_estimee']} heures
                                """
                            
                            corps += """
                            Veuillez vous assurer que toutes les dispositions nécessaires ont été prises.
                            
                            Cordialement,
                            Le système ManufacturingSoft
                            """
                            
                            send_notification_email(sujet, emails, corps)
                            logger.info(f"Notification de maintenance envoyée pour {len(maintenances)} maintenance(s) prévue(s) le {tomorrow}")
            except Exception as e:
                logger.error(f"Erreur lors de la vérification des maintenances: {str(e)}")
            finally:
                conn.close()

def run_stock_alert_check():
    """Vérification programmée des alertes de stock et envoi de notifications."""
    with app.app_context():
        conn = get_db_connection()
        if conn:
            try:
                with conn.cursor() as cursor:
                    # Stocks sous le seuil d'alerte
                    sql = """
                    SELECT s.*, p.nom as produit_nom, p.reference, p.categorie, e.nom as entrepot_nom,
                           (s.quantite / s.seuil_alerte) * 100 as pourcentage_seuil
                    FROM stocks s
                    JOIN produits p ON s.produit_id = p.id
                    JOIN entrepots e ON s.entrepot_id = e.id
                    WHERE s.actif = 1 AND p.actif = 1 AND s.quantite <= s.seuil_alerte
                    ORDER BY pourcentage_seuil ASC
                    """
                    cursor.execute(sql)
                    alertes = cursor.fetchall()
                    
                    if alertes:
                        # Compter les alertes critiques (moins de 50% du seuil)
                        alertes_critiques = [a for a in alertes if a['pourcentage_seuil'] < 50]
                        
                        if alertes_critiques:
                            # Récupérer les emails des gestionnaires de stock
                            cursor.execute("""
                                SELECT email FROM utilisateurs 
                                WHERE role IN ('manager', 'supervisor') AND actif = 1
                            """)
                            emails = [row['email'] for row in cursor.fetchall()]
                            
                            if emails:
                                # Construire le message
                                sujet = f"ALERTE CRITIQUE: {len(alertes_critiques)} produit(s) en rupture de stock imminente"
                                
                                corps = f"""
                                Bonjour,
                                
                                Ce message est une alerte automatique concernant des niveaux de stock critiques.
                                
                                Les produits suivants ont un niveau de stock inférieur à 50% du seuil d'alerte:
                                """
                                
                                for a in alertes_critiques:
                                    corps += f"""
                                    - {a['produit_nom']} ({a['reference']})
                                      Entrepôt: {a['entrepot_nom']}
                                      Quantité actuelle: {a['quantite']}
                                      Seuil d'alerte: {a['seuil_alerte']}
                                      Pourcentage du seuil: {a['pourcentage_seuil']:.2f}%
                                    """
                                
                                corps += """
                                Veuillez prendre les mesures nécessaires pour réapprovisionner ces stocks.
                                
                                Cordialement,
                                Le système ManufacturingSoft
                                """
                                
                                send_notification_email(sujet, emails, corps)
                                logger.info(f"Alerte stock critique envoyée pour {len(alertes_critiques)} produit(s)")
            except Exception as e:
                logger.error(f"Erreur lors de la vérification des alertes de stock: {str(e)}")
            finally:
                conn.close()

# =============================================================================
# DÉMARRAGE DE L'APPLICATION
# =============================================================================

if __name__ == '__main__':
    # Créer les répertoires nécessaires
    os.makedirs(app.config['UPLOAD_FOLDER'], exist_ok=True)
    os.makedirs(os.path.join(app.config['UPLOAD_FOLDER'], 'produits'), exist_ok=True)
    os.makedirs(os.path.join(app.config['UPLOAD_FOLDER'], 'qualite'), exist_ok=True)
    os.makedirs(os.path.join(app.config['UPLOAD_FOLDER'], 'maintenance'), exist_ok=True)
    os.makedirs(os.path.join(app.config['UPLOAD_FOLDER'], 'rapports'), exist_ok=True)
    os.makedirs(os.path.join(app.config['UPLOAD_FOLDER'], 'normes'), exist_ok=True)
    
    # Configurer les tâches planifiées
    from apscheduler.schedulers.background import BackgroundScheduler
    scheduler = BackgroundScheduler()
    scheduler.add_job(func=run_maintenance_check, trigger="cron", hour=9, minute=0)
    scheduler.add_job(func=run_stock_alert_check, trigger="cron", hour=8, minute=30)
    scheduler.start()
    
    app.run(debug=True, host='0.0.0.0', port=5000)