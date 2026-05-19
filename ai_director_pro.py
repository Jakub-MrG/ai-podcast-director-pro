import sounddevice as sd
import numpy as np
import time
import keyboard
import random
import threading
import json
import os
import webbrowser
import socket
import urllib.parse
import tkinter as tk
from tkinter import messagebox
import customtkinter as ctk
from obsws_python import ReqClient
from PIL import Image, ImageTk
import requests
import io
import qrcode
from flask import Flask, render_template_string, jsonify
import logging

# --- NASTAVENIE MODERNEHO VIZUALU ---
ctk.set_appearance_mode("Dark")
ctk.set_default_color_theme("blue")

CONFIG_FILE = "ai_director_settings.json"

DEFAULT_SETTINGS = {
    "user_name": "",       # NOVÉ PRE ONBOARDING
    "podcast_name": "",    # NOVÉ PRE ONBOARDING
    "obs_host": "localhost",
    "obs_port": "4455",
    "obs_password": "",
    "scene_host": "Scéna 1 (Hostiteľ)",
    "scene_guest": "Scéna 2 (Hosť)",
    "scene_wide_plain": "Scéna 3 (Celok)",
    "scene_wide_anim": "Scéna 4 (Menovky)",
    "mic1_device": "",
    "mic2_device": "",
    "mic3_device": "",
    "mic4_device": "",
    "kill_switch_hotkey": "ctrl+f12",
    "threshold_mic1": -30.0, 
    "threshold_mic2": -30.0,
    "threshold_mic3": -30.0,
    "threshold_mic4": -30.0,
    "speech_hangover": 0.8,
    "cooldown_time": 4.5,
    "wide_exit_sole_time": 3.5,
    "backchannel_filter": 1.5,
    "crosstalk_trigger_time": 1.5,
    "crosstalk_cooldown_time": 4.0,
    "rapid_exchange_limit": 4,
    "rapid_exchange_window": 7.0,
    "monologue_limit": 25.0,
    "silence_reset_time": 5.0,
    "manual_override_pause": 15.0,
    "nametag_min_gap": 7.0,
    "nametag_max_gap": 11.0,
    "nametag_lock_time": 30.0,
    "periodic_wide_min_gap": 4.0,
    "periodic_wide_max_gap": 6.0,
    "periodic_wide_lock_time": 40.0
}

HELP_TEXTS = {
    "threshold": "Prah citlivosti (Gate v dB): Určuje, aký silný musí byť zvuk, aby ho AI zaregistrovala ako reč. Funguje rovnako ako zvukový mixér v OBS.\n\nPre štúdiové mixpulty je ideál cca -30 dB až -20 dB.\nPre tiché webkamery skús okolo -45 dB.\n\nTIP: Použi tlačidlo [ AUTO ], hovor 4 sekundy a systém sám vypočíta ideálnu akustickú bránu.",
    "monologue": "Maximálny čas (v sekundách), počas ktorého kamera zostane na detaile jedného rečníka, ak hovorí dlhý monológ.\n\nPo uplynutí tohto času systém na chvíľu prepne na široký celok (Wide), aby prevetral vizuál a divák sa nenudil.",
    "hangover": "Hlasový most: Spája medzery medzi slabikami a slovami.\n\nKeď sa počas rozprávania na zlomok sekundy nadýchneš, AI ťa vďaka tomuto mostu neodstrihne. Odporúčaná hodnota je 0.8 sekundy.",
    "cooldown": "Ukotvenie detailu: Keď AI prepne kameru na rečníka, tento parameter jej zakáže urobiť ďalší strih po dobu X sekúnd.\n\nZabraňuje to chaotickému preblikávaniu kamier.",
    "wide_exit": "Opustenie celku: Ak ste na širokom zábere, rečník musí sám plynule rozprávať minimálne tento počet sekúnd, aby mu AI 'uverila', že ide o monológ a prepla na jeho detail.",
    "backchannel": "Filter krátkych reakcií (Backchanneling):\n\nAk niekto povie len krátke 'áno', 'hm' alebo 'presne', systém ho odignoruje a neprestrihne na neho kameru. Rečník musí hovoriť súvisle aspoň tento nastavený čas, aby mu systém 'uveril', že preberá slovo.",
    "exchange": "Limit skákania do reči: Ak si rečníci bleskovo vymenia slovo viackrát za sebou (napr. hádka alebo spoločný smiech), AI to vyhodnotí ako chaos a preventívne prepne na široký celok.",
    "crosstalk_trig": "Spúšťač spoločnej reči/smiechu:\n\nAk obaja rečníci hovoria naraz minimálne tento nastavený čas, systém to vyhodnotí ako prekrývanie (Cross-talk) a prepne na Celok, aby pokryl oboch.",
    "crosstalk_cool": "Kotva celku po spoločnej reči:\n\nKeď skončí hádka alebo spoločný smiech a rečníci stíchnu, AI nevystrelí okamžite späť na detail, ale upokojí scénu tak, že podrží široký záber na tento zadaný čas.",
    "nametags": "Automatické Menovky:\nSystém náhodne v určenom časovom intervale (Min - Max minút) vyvolá scénu s menovkami. \n\nPosuvník 'Čas uzamknutia' garantuje, že AI neprepne na iný záber, kým animácia menovky nedobehne do konca.",
    "periodic_wide": "Pravidelný vizuálny oddych:\nAby podcast nepôsobil ako ping-pong detailov, systém v tomto intervale cielene prepne na čistý široký celok."
}

def load_settings():
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                return {**DEFAULT_SETTINGS, **json.load(f)}
        except: pass
    return DEFAULT_SETTINGS

def save_settings(settings_dict):
    with open(CONFIG_FILE, "w", encoding="utf-8") as f:
        json.dump(settings_dict, f, indent=4, ensure_ascii=False)

app_settings = load_settings()
ai_enabled = False
obs_client = None
log_messages = []
active_obs_scene_name = "unknown"

live_levels = [0.0, 0.0, 0.0, 0.0]
display_levels_db = [-60.0, -60.0, -60.0, -60.0] 
trigger_reconnect = False
calibration_mode = [False, False, False, False] 

# --- GLOBÁLNE PREMENNÉ PRE TELEMETRIU A REMOTE ---
diag_monologue_time = 0.0
diag_exchange_count = 0
diag_cooldown = 0.0
diag_state_text = "Pripravený"
remote_command_queue = [] 

obs_is_recording = False
obs_record_time = "00:00:00"

def get_local_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except:
        return "127.0.0.1"

LOCAL_IP = get_local_ip()
FLASK_PORT = 5000

def get_audio_devices():
    devices = []
    try:
        for d in sd.query_devices():
            if d['max_input_channels'] > 0:
                name = d['name']
                if name not in devices: devices.append(name)
    except: pass
    return devices

audio_device_list = get_audio_devices()

# --- BACKEND LOGIKA (RÉŽIA) ---
def ai_director_backend_thread():
    global ai_enabled, obs_client, app_settings, live_levels, active_obs_scene_name, trigger_reconnect
    global diag_monologue_time, diag_exchange_count, diag_cooldown, diag_state_text, remote_command_queue
    global obs_is_recording, obs_record_time
    
    current_scene = "unknown"
    last_switch_time = time.time()
    speaker_start_time = time.time()
    last_spoken_time = time.time()
    last_obs_poll = time.time()
    locked_until = 0
    exchange_count = 0
    
    last_host_voice_time = 0.0
    last_guest_voice_time = 0.0
    host_floor_start_time = 0.0
    guest_floor_start_time = 0.0
    crosstalk_start_time = 0.0
    host_interrupt_start = 0.0
    guest_interrupt_start = 0.0
    
    next_nametag_time = time.time() + random.uniform(float(app_settings["nametag_min_gap"])*60, float(app_settings["nametag_max_gap"])*60)
    next_periodic_wide_time = time.time() + random.uniform(float(app_settings["periodic_wide_min_gap"])*60, float(app_settings["periodic_wide_max_gap"])*60)
    
    v1, v2, v3, v4 = 0.0, 0.0, 0.0, 0.0
    
    def cb_m1(indata, f, t, s): nonlocal v1; v1 = np.sqrt(np.mean(indata**2)) if len(indata)>0 else 0.0
    def cb_m2(indata, f, t, s): nonlocal v2; v2 = np.sqrt(np.mean(indata**2)) if len(indata)>0 else 0.0
    def cb_m3(indata, f, t, s): nonlocal v3; v3 = np.sqrt(np.mean(indata**2)) if len(indata)>0 else 0.0
    def cb_m4(indata, f, t, s): nonlocal v4; v4 = np.sqrt(np.mean(indata**2)) if len(indata)>0 else 0.0

    def add_log(text):
        timestamp = time.strftime("[%H:%M:%S]")
        log_messages.append(f"{timestamp} {text}")

    def safe_switch_scene(scene_name):
        if obs_client:
            try:
                obs_client.set_current_program_scene(scene_name)
                global active_obs_scene_name
                active_obs_scene_name = scene_name
                return True
            except Exception:
                add_log(f"❌ CHYBA: OBS nenašlo scénu '{scene_name}'! Skontroluj nastavenia.")
                return False
        return False

    streams = []

    def setup_connections():
        global obs_client, active_obs_scene_name
        nonlocal streams, v1, v2, v3, v4, current_scene
        
        for s in streams:
            try: s.stop(); s.close()
            except: pass
        streams.clear()
        v1, v2, v3, v4 = 0.0, 0.0, 0.0, 0.0

        add_log("--- INICIALIZÁCIA PRIPOJENÍ ---")

        if app_settings["obs_password"]:
            try:
                obs_client = ReqClient(host=app_settings["obs_host"], port=int(app_settings["obs_port"]), password=app_settings["obs_password"])
                add_log("✅ Úspešne pripojené k OBS WebSocket.")
                
                wide_scene = app_settings["scene_wide_plain"]
                if wide_scene:
                    time.sleep(0.5)
                    try:
                        obs_client.set_current_program_scene(wide_scene)
                        current_scene = wide_scene
                        active_obs_scene_name = wide_scene
                        add_log(f"Štart spojenia -> Vynútený začiatočný celok ({wide_scene}).")
                    except Exception as e:
                        add_log(f"Upozornenie: Nepodarilo sa vynútiť štartovací celok.")
            except Exception:
                obs_client = None
                add_log("❌ OBS nedostupné. Skontroluj heslo a port v nastaveniach.")

        def find_idx(name_str):
            if not name_str or name_str == "--- Vypnutý fader ---": return None
            for idx, d in enumerate(sd.query_devices()):
                if d['name'] == name_str and d['max_input_channels'] > 0: return idx
            return None

        idx1 = find_idx(app_settings["mic1_device"])
        idx2 = find_idx(app_settings["mic2_device"])
        idx3 = find_idx(app_settings["mic3_device"])
        idx4 = find_idx(app_settings["mic4_device"])

        try:
            if idx1 is not None: streams.append(sd.InputStream(device=idx1, channels=1, callback=cb_m1))
            if idx2 is not None: streams.append(sd.InputStream(device=idx2, channels=1, callback=cb_m2))
            if idx3 is not None: streams.append(sd.InputStream(device=idx3, channels=1, callback=cb_m3))
            if idx4 is not None: streams.append(sd.InputStream(device=idx4, channels=1, callback=cb_m4))
            
            if streams:
                for s in streams: s.start()
                add_log("✅ Vybrané mikrofóny sú aktívne a načítané.")
            else:
                add_log("⚠️ Žiadne mikrofóny neboli priradené.")
        except Exception as e:
            add_log(f"❌ CHYBA Zvuku: {str(e)[:50]}")

    setup_connections()

    while True:
        time.sleep(0.1)
        now = time.time()
        
        if obs_client and (now - last_obs_poll > 1.0):
            try:
                rec_stats = obs_client.get_record_status()
                obs_is_recording = rec_stats.output_active
                if obs_is_recording: obs_record_time = str(rec_stats.output_timecode)[:8]
                else: obs_record_time = "00:00:00"
                    
                real_scene = obs_client.get_current_program_scene().current_program_scene_name
                active_obs_scene_name = real_scene
            except: pass
            last_obs_poll = now
        
        if trigger_reconnect:
            setup_connections()
            trigger_reconnect = False

        live_levels[0], live_levels[1], live_levels[2], live_levels[3] = v1, v2, v3, v4
        diag_exchange_count = exchange_count
        
        if locked_until > now:
            diag_cooldown = locked_until - now
            diag_state_text = "Zablokované (Pauza)"
        else:
            diag_cooldown = 0.0
            diag_state_text = "Aktívne skenuje reč"

        if current_scene in [app_settings["scene_host"], app_settings["scene_guest"]]:
            diag_monologue_time = now - speaker_start_time
        else:
            diag_monologue_time = 0.0

        if remote_command_queue:
            cmd = remote_command_queue.pop(0)
            if cmd == "ai_toggle":
                ai_enabled = not ai_enabled
                add_log(f"[REMOTE] AI Režisér prepnutý: {'ZAPNUTÝ' if ai_enabled else 'VYPNUTÝ'}")
            elif cmd == "rec_toggle":
                if obs_client:
                    try:
                        obs_client.toggle_record()
                        add_log("[REMOTE] Odomknutý povel pre záznam v OBS.")
                    except Exception as e:
                        add_log(f"❌ CHYBA nahrávania: {e}")
            elif cmd in ["scene_host", "scene_guest", "scene_wide_plain", "scene_wide_anim"]:
                target_scene = app_settings[cmd]
                add_log(f"[REMOTE] Manuálny príkaz z mobilu -> {target_scene}")
                if safe_switch_scene(target_scene):
                    current_scene = target_scene
                    locked_until = now + float(app_settings["manual_override_pause"])
                    next_periodic_wide_time = max(next_periodic_wide_time, locked_until + 60.0)
                    next_nametag_time = max(next_nametag_time, locked_until + 60.0)
                    host_floor_start_time = 0.0; guest_floor_start_time = 0.0; exchange_count = 0
            continue

        if not ai_enabled:
            diag_state_text = "AI Vypnutá"
            current_scene = active_obs_scene_name
            continue
            
        managed_scenes = [app_settings["scene_host"], app_settings["scene_guest"], app_settings["scene_wide_plain"], app_settings["scene_wide_anim"]]
        
        if current_scene == app_settings["scene_wide_anim"] and now >= locked_until:
            add_log("--- MENOVKY --- Koniec animácie, vraciam obraz na Celok.")
            if safe_switch_scene(app_settings["scene_wide_plain"]):
                current_scene = app_settings["scene_wide_plain"]
                locked_until = now + 3.0
            continue

        if now < locked_until:
            last_spoken_time = now
            speaker_start_time = now
            continue

        if now >= next_nametag_time and current_scene != app_settings["scene_wide_anim"]:
            add_log(f"--- GRAFIKA --- Spúšťam animáciu Menoviek (Zámok na {app_settings['nametag_lock_time']}s).")
            if safe_switch_scene(app_settings["scene_wide_anim"]):
                current_scene = app_settings["scene_wide_anim"]
                last_switch_time = now; speaker_start_time = now
                locked_until = now + float(app_settings["nametag_lock_time"])
                gap = random.uniform(float(app_settings["nametag_min_gap"])*60, float(app_settings["nametag_max_gap"])*60)
                next_nametag_time = now + gap
                next_periodic_wide_time = max(next_periodic_wide_time, locked_until + 60.0)
            continue
            
        if now >= next_periodic_wide_time and current_scene not in [app_settings["scene_wide_plain"], app_settings["scene_wide_anim"]]:
            add_log(f"--- PACING --- Preventívny vizuálny oddych. Prepínam na Celok ({app_settings['periodic_wide_lock_time']}s).")
            if safe_switch_scene(app_settings["scene_wide_plain"]):
                current_scene = app_settings["scene_wide_plain"]
                last_switch_time = now; speaker_start_time = now
                locked_until = now + float(app_settings["periodic_wide_lock_time"])
                gap = random.uniform(float(app_settings["periodic_wide_min_gap"])*60, float(app_settings["periodic_wide_max_gap"])*60)
                next_periodic_wide_time = now + gap
                next_nametag_time = max(next_nametag_time, locked_until + 60.0)
            continue

        if active_obs_scene_name not in managed_scenes:
            current_scene = active_obs_scene_name
            continue
            
        if active_obs_scene_name != current_scene:
            add_log(f"[ZÁSAH] Manuálne prepnutie mimo AI -> '{active_obs_scene_name}'. Bezpečnostná pauza {app_settings['manual_override_pause']}s.")
            current_scene = active_obs_scene_name
            locked_until = now + float(app_settings["manual_override_pause"])
            next_periodic_wide_time = max(next_periodic_wide_time, locked_until + 60.0)
            next_nametag_time = max(next_nametag_time, locked_until + 60.0)
            continue

        th1_lin = 10 ** (float(app_settings["threshold_mic1"]) / 20)
        th2_lin = 10 ** (float(app_settings["threshold_mic2"]) / 20)
        th3_lin = 10 ** (float(app_settings["threshold_mic3"]) / 20)
        th4_lin = 10 ** (float(app_settings["threshold_mic4"]) / 20)

        host_active = (v1 > th1_lin) or (v4 > th4_lin)
        guest_active = (v2 > th2_lin) or (v3 > th3_lin)
        
        if host_active: last_host_voice_time = now
        if guest_active: last_guest_voice_time = now
        
        room_active = host_active or guest_active
        if room_active:
            silence_duration = now - last_spoken_time
            last_spoken_time = now
        else:
            silence_duration = 0

        # CROSS-TALK
        if host_active and guest_active:
            diag_state_text = "Prekrývanie reči (Cross-talk)"
            if crosstalk_start_time == 0.0: crosstalk_start_time = now
            if (now - crosstalk_start_time) >= float(app_settings["crosstalk_trigger_time"]):
                if current_scene not in [app_settings["scene_wide_plain"], app_settings["scene_wide_anim"]]:
                    add_log(f"[BRZDA] Detegovaný spoločný rozhovor/smiech ({app_settings['crosstalk_trigger_time']}s). Návrat na Celok.")
                    if safe_switch_scene(app_settings["scene_wide_plain"]):
                        current_scene = app_settings["scene_wide_plain"]
                        locked_until = now + float(app_settings["crosstalk_cooldown_time"])
                        crosstalk_start_time = 0.0
        else:
            crosstalk_start_time = 0.0

        host_holding = (now - last_host_voice_time) < float(app_settings["speech_hangover"])
        guest_holding = (now - last_guest_voice_time) < float(app_settings["speech_hangover"])

        if current_scene in [app_settings["scene_wide_plain"], app_settings["scene_wide_anim"]]:
            if host_holding and not guest_holding:
                diag_state_text = "Overujem reč (Hostiteľ)..."
                if host_floor_start_time == 0.0: host_floor_start_time = now
                guest_floor_start_time = 0.0
                if (now - host_floor_start_time) >= float(app_settings["wide_exit_sole_time"]):
                    add_log(f"Reč hostiteľa overená ({app_settings['wide_exit_sole_time']}s). Pripravujem strih na Detail -> Hostiteľ.")
                    if safe_switch_scene(app_settings["scene_host"]):
                        current_scene = app_settings["scene_host"]; last_switch_time = now; speaker_start_time = now; locked_until = now + float(app_settings["cooldown_time"])
            elif guest_holding and not host_holding:
                diag_state_text = "Overujem reč (Hosť)..."
                if guest_floor_start_time == 0.0: guest_floor_start_time = now
                host_floor_start_time = 0.0
                if (now - guest_floor_start_time) >= float(app_settings["wide_exit_sole_time"]):
                    add_log(f"Reč hosťa overená ({app_settings['wide_exit_sole_time']}s). Pripravujem strih na Detail -> Hosť.")
                    if safe_switch_scene(app_settings["scene_guest"]):
                        current_scene = app_settings["scene_guest"]; last_switch_time = now; speaker_start_time = now; locked_until = now + float(app_settings["cooldown_time"])
            else:
                host_floor_start_time = 0.0; guest_floor_start_time = 0.0
            continue
        else:
            if (now - speaker_start_time) > float(app_settings["monologue_limit"]):
                add_log(f"Prekročený max. čas monológu ({app_settings['monologue_limit']}s). Prevetrávam záber -> Celok.")
                if safe_switch_scene(app_settings["scene_wide_plain"]):
                    current_scene = app_settings["scene_wide_plain"]; locked_until = now + 4.0
                continue
                
            if room_active and silence_duration > float(app_settings["silence_reset_time"]):
                add_log(f"Dlhé ticho v štúdiu ({app_settings['silence_reset_time']}s). Návrat -> Celok.")
                if safe_switch_scene(app_settings["scene_wide_plain"]):
                    current_scene = app_settings["scene_wide_plain"]; locked_until = now + 4.0
                continue

            if host_holding and not guest_holding and current_scene != app_settings["scene_host"]:
                if host_interrupt_start == 0.0: host_interrupt_start = now
                diag_state_text = "Filtrujem reakciu (Hostiteľ)..."
                if (now - host_interrupt_start) >= float(app_settings["backchannel_filter"]):
                    if (now - last_switch_time) < float(app_settings["rapid_exchange_window"]): exchange_count += 1
                    else: exchange_count = 1
                    if exchange_count >= int(app_settings["rapid_exchange_limit"]):
                        add_log(f"[BRZDA] Rýchla prestrelka slov ({exchange_count}). Režisér ustupuje na Celok.")
                        if safe_switch_scene(app_settings["scene_wide_plain"]):
                            current_scene = app_settings["scene_wide_plain"]; locked_until = now + 6.0; exchange_count = 0
                    else:
                        add_log("Hostiteľ prevzal slovo. Pripravujem strih na Detail -> Hostiteľ.")
                        if safe_switch_scene(app_settings["scene_host"]):
                            current_scene = app_settings["scene_host"]; last_switch_time = now; speaker_start_time = now; locked_until = now + float(app_settings["cooldown_time"])
            else:
                host_interrupt_start = 0.0

            if guest_holding and not host_holding and current_scene != app_settings["scene_guest"]:
                if guest_interrupt_start == 0.0: guest_interrupt_start = now
                diag_state_text = "Filtrujem reakciu (Hosť)..."
                if (now - guest_interrupt_start) >= float(app_settings["backchannel_filter"]):
                    if (now - last_switch_time) < float(app_settings["rapid_exchange_window"]): exchange_count += 1
                    else: exchange_count = 1
                    if exchange_count >= int(app_settings["rapid_exchange_limit"]):
                        add_log(f"[BRZDA] Rýchla prestrelka slov ({exchange_count}). Režisér ustupuje na Celok.")
                        if safe_switch_scene(app_settings["scene_wide_plain"]):
                            current_scene = app_settings["scene_wide_plain"]; locked_until = now + 6.0; exchange_count = 0
                    else:
                        add_log("Hosť prevzal slovo. Pripravujem strih na Detail -> Hosť.")
                        if safe_switch_scene(app_settings["scene_guest"]):
                            current_scene = app_settings["scene_guest"]; last_switch_time = now; speaker_start_time = now; locked_until = now + float(app_settings["cooldown_time"])
            else:
                guest_interrupt_start = 0.0


# --- WEB SERVER (FLASK) ---
app_flask = Flask(__name__)
log = logging.getLogger('werkzeug')
log.setLevel(logging.ERROR)

HTML_TEMPLATE = """
<!DOCTYPE html>
<html lang="sk">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Mr. G | Studio Remote</title>
    <style>
        body { background-color: #0f172a; color: #f8fafc; font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif; text-align: center; margin: 0; padding: 15px; user-select: none; }
        h2 { color: #deff9a; margin-top: 5px; margin-bottom: 5px; font-size: 24px;}
        .status-box { background-color: #1e293b; padding: 12px; border-radius: 12px; margin-bottom: 15px; box-shadow: 0 4px 6px rgba(0,0,0,0.3); }
        .status-text { font-size: 13px; color: #94a3b8; margin: 5px 0;}
        .highlight { color: #38bdf8; font-weight: bold; }
        
        .btn { display: block; width: 100%; padding: 18px; font-size: 16px; font-weight: bold; border: none; border-radius: 12px; cursor: pointer; color: white; transition: 0.2s; box-shadow: 0 4px 6px rgba(0,0,0,0.2);}
        .btn:active { transform: scale(0.96); }
        
        .btn-ai { background-color: #10b981; margin-top: 15px;}
        .btn-ai.off { background-color: #ef4444; }
        
        .btn-rec { background-color: #dc2626; border: 2px solid #f87171;}
        .btn-rec.recording { background-color: #000000; color: #ef4444; border: 2px solid #ef4444; animation: pulse 2s infinite; }
        
        .btn-scene { background-color: #3b82f6; display: flex; align-items: center; justify-content: center; height: 80px; box-sizing: border-box;}
        .btn-scene.active { background-color: #10b981 !important; border: 3px solid white; box-shadow: 0 0 15px #10b981; color: white;}
        
        .grid-container { display: grid; grid-template-columns: 1fr 1fr; gap: 12px; margin-top: 20px;}
        
        .promo-banner { background-color: #000000; padding: 15px; border-radius: 12px; margin-top: 30px; text-align: center; border: 1px solid #334155;}
        .btn-sub { background-color: #ef4444; padding: 12px; font-size: 15px;}
        
        @keyframes pulse {
            0% { box-shadow: 0 0 0 0 rgba(239, 68, 68, 0.7); }
            70% { box-shadow: 0 0 0 10px rgba(239, 68, 68, 0); }
            100% { box-shadow: 0 0 0 0 rgba(239, 68, 68, 0); }
        }
    </style>
</head>
<body>
    <h2>STUDIO REMOTE</h2>
    <div class="status-box">
        <div class="status-text" id="ai_status">AI Status: Načítavam...</div>
        <div class="status-text">OBS Scéna: <span class="highlight" id="obs_scene">Načítavam...</span></div>
    </div>
    <button class="btn btn-rec" id="rec_btn" onclick="action('rec_toggle')">Nahrávanie v OBS</button>
    <button class="btn btn-ai" id="ai_btn" onclick="action('ai_toggle')">Štart AI Réžie</button>
    <h3 style="margin-top: 25px; margin-bottom: 0; color: #64748b; font-size: 15px;">Manuálny Strih Kamier</h3>
    <div class="grid-container">
        <button id="btn_s_host" class="btn btn-scene" onclick="action('scene_host')">{{ s_host }}</button>
        <button id="btn_s_guest" class="btn btn-scene" onclick="action('scene_guest')">{{ s_guest }}</button>
        <button id="btn_s_wide" class="btn btn-scene" onclick="action('scene_wide_plain')">{{ s_wide }}</button>
        <button id="btn_s_anim" class="btn btn-scene" style="background-color: #8b5cf6;" onclick="action('scene_wide_anim')">{{ s_anim }}</button>
    </div>
    <div class="promo-banner">
        <h3 style="color: #deff9a; margin-top: 0; margin-bottom: 5px;">#NEMAMCASNUDITSA</h3>
        <p class="status-text" style="margin-bottom: 15px;">Vystúp z komfortnej zóny a buď lepší ako včera...</p>
        <button class="btn btn-sub" onclick="window.open('https://www.youtube.com/@JakubMrG?sub_confirmation=1', '_blank')">Odoberať Jakub Mr. G</button>
    </div>
    <script>
        const sceneNames = {
            'btn_s_host': '{{ s_host }}',
            'btn_s_guest': '{{ s_guest }}',
            'btn_s_wide': '{{ s_wide }}',
            'btn_s_anim': '{{ s_anim }}'
        };
        function action(cmd) { 
            fetch('/api/' + cmd);
            if (window.navigator && window.navigator.vibrate) { navigator.vibrate(50); }
        }
        setInterval(() => {
            fetch('/api/status').then(r => r.json()).then(d => {
                document.getElementById('obs_scene').innerText = d.scene;
                document.getElementById('ai_status').innerText = 'AI Status: ' + d.ai_state;
                for (const [btnId, sceneName] of Object.entries(sceneNames)) {
                    let btn = document.getElementById(btnId);
                    if (d.scene === sceneName) { btn.classList.add('active'); } 
                    else { btn.classList.remove('active'); }
                }
                let aiBtn = document.getElementById('ai_btn');
                if(d.ai_enabled) { aiBtn.innerText = 'ZASTAVIŤ AI (Kill Switch)'; aiBtn.className = 'btn btn-ai off'; }
                else { aiBtn.innerText = 'ŠTART AI RÉŽIE'; aiBtn.className = 'btn btn-ai'; }
                let recBtn = document.getElementById('rec_btn');
                if(d.is_recording) { 
                    recBtn.innerText = '🔴 NAHRÁVA SA (' + d.record_time + ')'; 
                    recBtn.className = 'btn btn-rec recording'; 
                } else { 
                    recBtn.innerText = 'Štart nahrávania v OBS'; 
                    recBtn.className = 'btn btn-rec'; 
                }
            }).catch(e => console.log("Connection error"));
        }, 800);
    </script>
</body>
</html>
"""

@app_flask.route('/')
def index():
    return render_template_string(HTML_TEMPLATE,
        s_host=app_settings["scene_host"],
        s_guest=app_settings["scene_guest"],
        s_wide=app_settings["scene_wide_plain"],
        s_anim=app_settings["scene_wide_anim"]
    )

@app_flask.route('/api/status')
def api_status():
    return jsonify({
        "scene": active_obs_scene_name,
        "ai_state": diag_state_text,
        "ai_enabled": ai_enabled,
        "is_recording": obs_is_recording,
        "record_time": obs_record_time
    })

@app_flask.route('/api/<command>')
def api_command(command):
    global remote_command_queue
    remote_command_queue.append(command)
    return jsonify({"status": "queued"})

def start_flask_server():
    try: app_flask.run(host='0.0.0.0', port=FLASK_PORT, threaded=True)
    except: pass


# --- FRONTEND GRAFIKA ---
class AIDirectorProGUI(ctk.CTk):
    def __init__(self):
        super().__init__()
        
        self.title("AI Podcast Director Pro | by Jakub Mr. G")
        self.geometry("850x740")
        self.minsize(550, 720) 
        
        self.apply_brand_icon()
        self.pacing_controls = {} 
        
        # LOGIKA ONBOARDINGU (Prvé spustenie)
        if not app_settings.get("user_name"):
            self.withdraw() # Skryje hlavné okno
            self.show_welcome_screen()
        else:
            self.build_main_app()

    def show_welcome_screen(self):
        self.welcome_win = ctk.CTkToplevel(self)
        self.welcome_win.title("Vitaj v AI Director Pro")
        self.welcome_win.geometry("550x550")
        self.welcome_win.resizable(False, False)
        self.welcome_win.attributes("-topmost", True)
        self.welcome_win.protocol("WM_DELETE_WINDOW", self.destroy) # Zavrie celú appku ak to krížikuje
        
        container = ctk.CTkFrame(self.welcome_win, fg_color="transparent")
        container.pack(expand=True, fill="both", padx=40, pady=40)
        
        ctk.CTkLabel(container, text="👋 Vitaj v štúdiu!", font=ctk.CTkFont(family="Urbanist", size=28, weight="bold"), text_color="#deff9a").pack(pady=(0, 10))
        
        intro_text = ("Ahoj, som Jakub Mr. G. Tento nástroj som vyvinul, aby som pomohol tvorcom zefektívniť ich prácu a vyhol sa nude v strižni.\n\n"
                      "Kým ťa pustím do režisérskeho kresla, poďme si to trochu prispôsobiť:")
        ctk.CTkLabel(container, text=intro_text, font=ctk.CTkFont(size=14), wraplength=450, justify="center").pack(pady=(0, 20))
        
        self.ent_user = ctk.CTkEntry(container, placeholder_text="Tvoje meno alebo prezývka", width=300, height=40)
        self.ent_user.pack(pady=10)
        
        self.ent_pod = ctk.CTkEntry(container, placeholder_text="Názov tvojho podcastu / projektu", width=300, height=40)
        self.ent_pod.pack(pady=10)
        
        ctk.CTkLabel(container, text="Najväčšou odmenou pre mňa bude, ak ma podporíš na YouTube,\nalebo mi dáš vedieť, že softvér používaš.", font=ctk.CTkFont(size=13), text_color="#94a3b8").pack(pady=(20, 10))
        
        btn_frame = ctk.CTkFrame(container, fg_color="transparent")
        btn_frame.pack(fill="x", pady=10)
        
        ctk.CTkButton(btn_frame, text="Odoberať Jakub Mr. G", fg_color="#ef4444", hover_color="#dc2626", command=self.action_open_youtube_promo).pack(side="left", expand=True, padx=5)
        ctk.CTkButton(btn_frame, text="✉️ Poslať mi pozdrav", fg_color="#2563eb", hover_color="#1d4ed8", command=self.action_send_hello).pack(side="left", expand=True, padx=5)
        
        ctk.CTkButton(container, text="VSTÚPIŤ DO RÉŽIE A ZAČAŤ", fg_color="#10b981", hover_color="#059669", font=ctk.CTkFont(weight="bold"), height=50, command=self.finish_onboarding).pack(fill="x", pady=(20, 0))

    def action_send_hello(self):
        u_name = self.ent_user.get().strip() or "Tvorca"
        p_name = self.ent_pod.get().strip() or "môj podcast"
        body = f"Ahoj Jakub,\n\ntu je {u_name}. Idem práve otestovať tvoj AI Podcast Director Pro na mojom projekte '{p_name}'!\n\nPozdravujem."
        subject = "Ahoj, idem otestovať AI Director Pro!"
        try: webbrowser.open(f"mailto:mrg.golive@gmail.com?subject={urllib.parse.quote(subject)}&body={urllib.parse.quote(body)}")
        except: pass

    def finish_onboarding(self):
        app_settings["user_name"] = self.ent_user.get().strip() or "Režisér"
        app_settings["podcast_name"] = self.ent_pod.get().strip() or "Podcast"
        save_settings(app_settings)
        self.welcome_win.destroy()
        self.deiconify() # Ukáže hlavné okno
        self.build_main_app()

    def build_main_app(self):
        self.register_kill_switch()
        
        header_frame = ctk.CTkFrame(master=self, fg_color="transparent")
        header_frame.pack(side="top", fill="x", padx=25, pady=(20, 5))
        
        u_name = app_settings.get("user_name", "")
        title_text = f"AI PODCAST DIRECTOR PRO | Réžia: {u_name}" if u_name else "AI PODCAST DIRECTOR PRO"
        
        lbl_title = ctk.CTkLabel(master=header_frame, text=title_text, font=ctk.CTkFont(family="Urbanist", size=24, weight="bold"), text_color="#deff9a")
        lbl_title.pack(anchor="w")
        
        lbl_subtitle = ctk.CTkLabel(master=header_frame, text="Automated Multi-Camera Switcher Engine  •  Developed by Jakub Mr. G", font=ctk.CTkFont(family="Urbanist", size=13, weight="normal"), text_color="#64748b")
        lbl_subtitle.pack(anchor="w", pady=(2, 0))

        lbl_motto = ctk.CTkLabel(master=header_frame, text='„Vystúp z komfortnej zóny a buď lepší ako včera...“ | www.jakubmrg.sk', font=ctk.CTkFont(family="Urbanist", size=13, slant="italic"), text_color="#38bdf8", cursor="hand2")
        lbl_motto.pack(anchor="w", pady=(5, 0))
        lbl_motto.bind("<Button-1>", lambda e: webbrowser.open("https://www.jakubmrg.sk"))

        footer_frame = ctk.CTkFrame(master=self, fg_color="#0d0d0d", height=65, corner_radius=0)
        footer_frame.pack(side="bottom", fill="x")
        
        lbl_support = ctk.CTkLabel(master=footer_frame, text="Páči sa ti tento nástroj? Podpor tvorcu odberom a počúvaj podcast #NEMAMCASNUDITSA!", font=ctk.CTkFont(family="Urbanist", size=13, weight="normal"), text_color="#94a3b8")
        lbl_support.pack(side="left", padx=25, pady=18)
        
        btn_sub = ctk.CTkButton(master=footer_frame, text="Odoberaj Jakub Mr. G", fg_color="#ef4444", hover_color="#dc2626", font=ctk.CTkFont(family="Urbanist", size=13, weight="bold"), height=32, command=self.action_open_youtube_promo)
        btn_sub.pack(side="right", padx=25, pady=18)

        self.tabview = ctk.CTkTabview(self)
        self.tabview.pack(side="top", padx=20, pady=5, fill="both", expand=True)
        
        self.tab_obs = self.tabview.add("OBS Connection")
        self.tab_settings = self.tabview.add("Settings")
        self.tab_monitor = self.tabview.add("Monitor")
        self.tab_remote = self.tabview.add("Mobilný Ovládač") 
        self.tab_about = self.tabview.add("O autorovi")
        
        self.build_obs_tab()
        self.build_settings_tab()
        self.build_monitor_tab()
        self.build_remote_tab()
        self.build_about_tab()
        
        self.update_gui_loop()

    def apply_brand_icon(self):
        try:
            url = "https://jakubmrg.sk/wp-content/uploads/2026/04/jmg-for-thumbnail-mic-e1776764309829.png"
            response = requests.get(url, timeout=3)
            img_data = Image.open(io.BytesIO(response.content))
            photo = ImageTk.PhotoImage(img_data)
            self.iconphoto(True, photo)
        except Exception: pass

    def action_open_youtube_promo(self):
        webbrowser.open("https://www.youtube.com/@JakubMrG?sub_confirmation=1")

    def register_kill_switch(self):
        try: keyboard.unhook_all()
        except: pass
        keyboard.add_hotkey(app_settings["kill_switch_hotkey"], self.toggle_ai_via_hotkey)

    def toggle_ai_via_hotkey(self):
        global ai_enabled
        ai_enabled = not ai_enabled
        log_messages.append(f"[HOTKEY] AI Režisér prepnutý: {'ZAPNUTÝ' if ai_enabled else 'VYPNUTÝ'}")

    def action_toggle_ai_button(self):
        global ai_enabled
        ai_enabled = not ai_enabled
        log_messages.append(f"[TLAČIDLO] AI Režisér prepnutý: {'ZAPNUTÝ' if ai_enabled else 'VYPNUTÝ'}")

    def show_help(self, title, text_key):
        messagebox.showinfo(title, HELP_TEXTS.get(text_key, "Nápoveda nie je k dispozícii."))

    def build_obs_tab(self):
        self.scroll_obs = ctk.CTkScrollableFrame(self.tab_obs, fg_color="transparent")
        self.scroll_obs.pack(fill="both", expand=True)
        
        lbl_obs = ctk.CTkLabel(self.scroll_obs, text="OBS WebSocket Server", font=ctk.CTkFont(size=16, weight="bold"))
        lbl_obs.grid(row=0, column=0, columnspan=2, padx=20, pady=10, sticky="w")
        
        ctk.CTkLabel(self.scroll_obs, text="IP Adresa:").grid(row=1, column=0, padx=20, pady=5, sticky="e")
        self.ent_host = ctk.CTkEntry(self.scroll_obs, width=180); self.ent_host.insert(0, app_settings["obs_host"])
        self.ent_host.grid(row=1, column=1, padx=20, pady=5, sticky="w")
        
        ctk.CTkLabel(self.scroll_obs, text="Port:").grid(row=2, column=0, padx=20, pady=5, sticky="e")
        self.ent_port = ctk.CTkEntry(self.scroll_obs, width=180); self.ent_port.insert(0, app_settings["obs_port"])
        self.ent_port.grid(row=2, column=1, padx=20, pady=5, sticky="w")
        
        ctk.CTkLabel(self.scroll_obs, text="Heslo:").grid(row=3, column=0, padx=20, pady=5, sticky="e")
        self.ent_pass = ctk.CTkEntry(self.scroll_obs, width=180, show="*"); self.ent_pass.insert(0, app_settings["obs_password"])
        self.ent_pass.grid(row=3, column=1, padx=20, pady=5, sticky="w")

        lbl_scenes = ctk.CTkLabel(self.scroll_obs, text="Mapovanie scény (OBS)", font=ctk.CTkFont(size=16, weight="bold"))
        lbl_scenes.grid(row=4, column=0, columnspan=2, padx=20, pady=15, sticky="w")
        
        ctk.CTkLabel(self.scroll_obs, text="Hostiteľ Detail:").grid(row=5, column=0, padx=20, pady=5, sticky="e")
        self.ent_s_host = ctk.CTkEntry(self.scroll_obs, width=180); self.ent_s_host.insert(0, app_settings["scene_host"])
        self.ent_s_host.grid(row=5, column=1, padx=20, pady=5, sticky="w")
        
        ctk.CTkLabel(self.scroll_obs, text="Hosť Detail:").grid(row=6, column=0, padx=20, pady=5, sticky="e")
        self.ent_s_guest = ctk.CTkEntry(self.scroll_obs, width=180); self.ent_s_guest.insert(0, app_settings["scene_guest"])
        self.ent_s_guest.grid(row=6, column=1, padx=20, pady=5, sticky="w")
        
        ctk.CTkLabel(self.scroll_obs, text="Čistý Celok:").grid(row=7, column=0, padx=20, pady=5, sticky="e")
        self.ent_s_wide = ctk.CTkEntry(self.scroll_obs, width=180); self.ent_s_wide.insert(0, app_settings["scene_wide_plain"])
        self.ent_s_wide.grid(row=7, column=1, padx=20, pady=5, sticky="w")
        
        ctk.CTkLabel(self.scroll_obs, text="Celok Menovky:").grid(row=8, column=0, padx=20, pady=5, sticky="e")
        self.ent_s_anim = ctk.CTkEntry(self.scroll_obs, width=180); self.ent_s_anim.insert(0, app_settings["scene_wide_anim"])
        self.ent_s_anim.grid(row=8, column=1, padx=20, pady=5, sticky="w")

        lbl_audio = ctk.CTkLabel(self.scroll_obs, text="Audio Hardware & Skratky", font=ctk.CTkFont(size=16, weight="bold"))
        lbl_audio.grid(row=0, column=2, columnspan=2, padx=40, pady=10, sticky="w")
        
        devices = ["--- Vypnutý fader ---"] + audio_device_list
        
        ctk.CTkLabel(self.scroll_obs, text="Mic 1 (Hostiteľ):").grid(row=1, column=2, padx=40, pady=5, sticky="e")
        self.dd_m1 = ctk.CTkOptionMenu(self.scroll_obs, values=devices, width=180)
        self.dd_m1.grid(row=1, column=3, padx=10, pady=5, sticky="w")
        if app_settings["mic1_device"] in devices: self.dd_m1.set(app_settings["mic1_device"])
        
        ctk.CTkLabel(self.scroll_obs, text="Mic 2 (Hosť):").grid(row=2, column=2, padx=40, pady=5, sticky="e")
        self.dd_m2 = ctk.CTkOptionMenu(self.scroll_obs, values=devices, width=180)
        self.dd_m2.grid(row=2, column=3, padx=10, pady=5, sticky="w")
        if app_settings["mic2_device"] in devices: self.dd_m2.set(app_settings["mic2_device"])
        
        ctk.CTkLabel(self.scroll_obs, text="Mic 3 (Hosť Extra):").grid(row=3, column=2, padx=40, pady=5, sticky="e")
        self.dd_m3 = ctk.CTkOptionMenu(self.scroll_obs, values=devices, width=180)
        self.dd_m3.grid(row=3, column=3, padx=10, pady=5, sticky="w")
        if app_settings["mic3_device"] in devices: self.dd_m3.set(app_settings["mic3_device"])
        
        ctk.CTkLabel(self.scroll_obs, text="Mic 4 (Host Extra):").grid(row=4, column=2, padx=40, pady=5, sticky="e")
        self.dd_m4 = ctk.CTkOptionMenu(self.scroll_obs, values=devices, width=180)
        self.dd_m4.grid(row=4, column=3, padx=10, pady=5, sticky="w")
        if app_settings["mic4_device"] in devices: self.dd_m4.set(app_settings["mic4_device"])

        ctk.CTkLabel(self.scroll_obs, text="Kill Switch Skratka:").grid(row=6, column=2, padx=40, pady=5, sticky="e")
        self.ent_hotkey = ctk.CTkEntry(self.scroll_obs, width=180); self.ent_hotkey.insert(0, app_settings["kill_switch_hotkey"])
        self.ent_hotkey.grid(row=6, column=3, padx=10, pady=5, sticky="w")

        self.btn_save_basic = ctk.CTkButton(self.scroll_obs, text="ULOŽIŤ A REŠTARTOVAŤ PRIPOJENIA", fg_color="#10b981", hover_color="#059669", height=42, font=ctk.CTkFont(weight="bold"), command=self.action_save_basic_setup)
        self.btn_save_basic.grid(row=10, column=0, columnspan=4, padx=20, pady=35, sticky="ew")

    def action_save_basic_setup(self):
        global app_settings, trigger_reconnect
        app_settings["obs_host"] = self.ent_host.get()
        app_settings["obs_port"] = self.ent_port.get()
        app_settings["obs_password"] = self.ent_pass.get()
        app_settings["scene_host"] = self.ent_s_host.get()
        app_settings["scene_guest"] = self.ent_s_guest.get()
        app_settings["scene_wide_plain"] = self.ent_s_wide.get()
        app_settings["scene_wide_anim"] = self.ent_s_anim.get()
        app_settings["mic1_device"] = self.dd_m1.get() if self.dd_m1.get() != "--- Vypnutý fader ---" else ""
        app_settings["mic2_device"] = self.dd_m2.get() if self.dd_m2.get() != "--- Vypnutý fader ---" else ""
        app_settings["mic3_device"] = self.dd_m3.get() if self.dd_m3.get() != "--- Vypnutý fader ---" else ""
        app_settings["mic4_device"] = self.dd_m4.get() if self.dd_m4.get() != "--- Vypnutý fader ---" else ""
        app_settings["kill_switch_hotkey"] = self.ent_hotkey.get()
        
        save_settings(app_settings)
        self.register_kill_switch()
        trigger_reconnect = True
        self.tabview.set("Monitor")

    def build_settings_tab(self):
        self.scroll_settings = ctk.CTkScrollableFrame(self.tab_settings, fg_color="transparent")
        self.scroll_settings.pack(fill="both", expand=True)

        frame_th_title = ctk.CTkFrame(self.scroll_settings, fg_color="transparent")
        frame_th_title.pack(fill="x", padx=10, pady=(5,0))
        ctk.CTkLabel(frame_th_title, text="Brány citlivosti mikrofónov (Decibely / dB)", font=ctk.CTkFont(size=15, weight="bold")).pack(side="left")
        ctk.CTkButton(frame_th_title, text="[ ? ]", width=30, height=24, fg_color="#334155", hover_color="#475569", command=lambda: self.show_help("Brány citlivosti", "threshold")).pack(side="left", padx=10)

        self.sliders_mic = []
        self.labels_mic = []
        self.auto_buttons = []
        names = ["Mic 1", "Mic 2", "Mic 3", "Mic 4"]
        keys = ["threshold_mic1", "threshold_mic2", "threshold_mic3", "threshold_mic4"]

        for i in range(4):
            frame = ctk.CTkFrame(self.scroll_settings, fg_color="transparent")
            frame.pack(fill="x", padx=10, pady=2)
            
            btn_auto = ctk.CTkButton(frame, text="[ AUTO ]", width=60, fg_color="#4f46e5", hover_color="#4338ca", command=lambda idx=i: threading.Thread(target=self.run_auto_calibration, args=(idx,)).start())
            btn_auto.pack(side="left", padx=(0, 10))
            self.auto_buttons.append(btn_auto)

            ctk.CTkLabel(frame, text=f"{names[i]}:", width=50, anchor="w").pack(side="left")
            
            sl = ctk.CTkSlider(frame, from_=-60.0, to=0.0, number_of_steps=120, command=lambda v, idx=i: self.update_mic_slider_label(idx, v))
            sl.set(float(app_settings[keys[i]]))
            sl.pack(side="left", fill="x", expand=True, padx=10)
            
            lbl = ctk.CTkLabel(frame, text=f"{sl.get():.1f} dB", width=60)
            lbl.pack(side="right")
            self.sliders_mic.append(sl); self.labels_mic.append(lbl)

        frame_pac_title = ctk.CTkFrame(self.scroll_settings, fg_color="transparent")
        frame_pac_title.pack(fill="x", padx=10, pady=(20, 5))
        ctk.CTkLabel(frame_pac_title, text="Ladenie dynamiky strihu (Pacing Parameters)", font=ctk.CTkFont(size=15, weight="bold")).pack(side="left")

        frame_presets = ctk.CTkFrame(self.scroll_settings, fg_color="transparent")
        frame_presets.pack(fill="x", padx=10, pady=(5, 10))
        
        btn_dyn = ctk.CTkButton(frame_presets, text="⚡ DYNAMICKÝ", fg_color="#ea580c", hover_color="#c2410c", font=ctk.CTkFont(weight="bold"), command=lambda: self.action_apply_preset("dynamic"))
        btn_dyn.pack(side="left", expand=True, padx=5)
        
        btn_std = ctk.CTkButton(frame_presets, text="🎙️ BEŽNÝ", fg_color="#2563eb", hover_color="#1d4ed8", font=ctk.CTkFont(weight="bold"), command=lambda: self.action_apply_preset("standard"))
        btn_std.pack(side="left", expand=True, padx=5)
        
        btn_edu = ctk.CTkButton(frame_presets, text="🧠 EDUKATÍVNY", fg_color="#8b5cf6", hover_color="#7c3aed", font=ctk.CTkFont(weight="bold"), command=lambda: self.action_apply_preset("educational"))
        btn_edu.pack(side="left", expand=True, padx=5)

        self.sl_monologue, self.lbl_monologue = self.create_pacing_slider("Max čas na detaile (s):", 5.0, 300.0, "monologue_limit", help_key="monologue")
        self.sl_hangover, self.lbl_hangover = self.create_pacing_slider("Hlasový most (s):", 0.1, 3.0, "speech_hangover", help_key="hangover")
        self.sl_cooldown, self.lbl_cooldown = self.create_pacing_slider("Kotva detailu po strihu (s):", 1.0, 30.0, "cooldown_time", help_key="cooldown")
        self.sl_wide_exit, self.lbl_wide_exit = self.create_pacing_slider("Zotrvanie reči pre strih z celku (s):", 0.5, 20.0, "wide_exit_sole_time", help_key="wide_exit")
        self.sl_backchan, self.lbl_backchan = self.create_pacing_slider("Ignorovať krátke reakcie (s):", 0.1, 3.0, "backchannel_filter", help_key="backchannel")
        self.sl_cross_trig, self.lbl_cross_trig = self.create_pacing_slider("Spúšťač spoločnej reči (s):", 1.5, 5.0, "crosstalk_trigger_time", help_key="crosstalk_trig")
        self.sl_cross_cool, self.lbl_cross_cool = self.create_pacing_slider("Kotva celku po spoloč. reči (s):", 4.5, 15.0, "crosstalk_cooldown_time", help_key="crosstalk_cool")
        self.sl_exchange, self.lbl_exchange = self.create_pacing_slider("Limit skákania do reči:", 2.0, 10.0, "rapid_exchange_limit", is_int=True, help_key="exchange")

        frame_auto_title = ctk.CTkFrame(self.scroll_settings, fg_color="transparent")
        frame_auto_title.pack(fill="x", padx=10, pady=(20, 5))
        ctk.CTkLabel(frame_auto_title, text="Automatické prvky a Grafika", font=ctk.CTkFont(size=15, weight="bold")).pack(side="left")
        
        self.sl_nt_min, self.lbl_nt_min = self.create_pacing_slider("Menovky: Min interval (min):", 2.0, 20.0, "nametag_min_gap", help_key="nametags")
        self.sl_nt_max, self.lbl_nt_max = self.create_pacing_slider("Menovky: Max interval (min):", 2.0, 25.0, "nametag_max_gap", help_key="nametags")
        self.sl_nt_lock, self.lbl_nt_lock = self.create_pacing_slider("Menovky: Zámok grafiky (s):", 10.0, 60.0, "nametag_lock_time", help_key="nametags")
        self.sl_pw_min, self.lbl_pw_min = self.create_pacing_slider("Oddych (Wide): Min interval (min):", 2.0, 20.0, "periodic_wide_min_gap", help_key="periodic_wide")
        self.sl_pw_max, self.lbl_pw_max = self.create_pacing_slider("Oddych (Wide): Max interval (min):", 2.0, 25.0, "periodic_wide_max_gap", help_key="periodic_wide")
        self.sl_pw_lock, self.lbl_pw_lock = self.create_pacing_slider("Oddych (Wide): Zámok (s):", 10.0, 120.0, "periodic_wide_lock_time", help_key="periodic_wide")

        ctk.CTkButton(self.scroll_settings, text="AKTUALIZOVAŤ REŽISÉRSKE TEMPO", fg_color="#2563eb", hover_color="#1d4ed8", height=40, font=ctk.CTkFont(weight="bold"), command=self.action_save_pacing_settings).pack(fill="x", padx=10, pady=25)

    def action_apply_preset(self, preset_type):
        if preset_type == "dynamic":
            vals = {"monologue_limit": 15.0, "speech_hangover": 0.5, "cooldown_time": 2.0, "wide_exit_sole_time": 2.0, "backchannel_filter": 0.8, "crosstalk_trigger_time": 1.5, "crosstalk_cooldown_time": 4.5, "rapid_exchange_limit": 6}
        elif preset_type == "standard":
            vals = {"monologue_limit": 25.0, "speech_hangover": 0.8, "cooldown_time": 4.5, "wide_exit_sole_time": 3.5, "backchannel_filter": 1.5, "crosstalk_trigger_time": 2.0, "crosstalk_cooldown_time": 6.0, "rapid_exchange_limit": 4}
        elif preset_type == "educational":
            vals = {"monologue_limit": 45.0, "speech_hangover": 1.5, "cooldown_time": 7.0, "wide_exit_sole_time": 5.0, "backchannel_filter": 2.5, "crosstalk_trigger_time": 3.0, "crosstalk_cooldown_time": 10.0, "rapid_exchange_limit": 2}

        for key, val in vals.items():
            app_settings[key] = val
            if key in self.pacing_controls:
                sl, lbl, is_int = self.pacing_controls[key]
                sl.set(float(val))
                lbl.configure(text=str(int(val)) if is_int else str(round(float(val), 1)))

        save_settings(app_settings)
        log_messages.append(f"--- Továrenské nastavenie aplikované: Profil {preset_type.upper()} ---")

    def run_auto_calibration(self, idx):
        global live_levels, app_settings, calibration_mode
        if calibration_mode[idx]: return 
        calibration_mode[idx] = True
        
        btn = self.auto_buttons[idx]
        btn.configure(text="HOVOR 4s", fg_color="#dc2626", hover_color="#dc2626") 
        
        samples = []
        for _ in range(40): 
            time.sleep(0.1)
            val = live_levels[idx]
            if val > 0.0001: samples.append(val)
                
        if len(samples) > 5:
            avg_lin = sum(samples) / len(samples)
            ideal_thresh_lin = avg_lin * 0.35 
            ideal_thresh_db = round(20 * np.log10(ideal_thresh_lin), 1)
            if ideal_thresh_db < -59.0: ideal_thresh_db = -59.0
            if ideal_thresh_db > -1.0: ideal_thresh_db = -1.0
            
            self.after(0, self.apply_calibration_result, idx, ideal_thresh_db)
        else:
            self.after(0, self.calibration_failed, idx)
            
        calibration_mode[idx] = False

    def apply_calibration_result(self, idx, new_db_val):
        self.sliders_mic[idx].set(new_db_val)
        self.update_mic_slider_label(idx, new_db_val)
        self.action_save_pacing_settings()
        btn = self.auto_buttons[idx]
        btn.configure(text="HOTOVO", fg_color="#10b981", hover_color="#10b981") 
        self.after(2000, lambda: btn.configure(text="[ AUTO ]", fg_color="#4f46e5", hover_color="#4338ca"))
        log_messages.append(f"[KALIBRÁCIA] Mic {idx+1} bol ideálne nastavený na Threshold: {new_db_val:.1f} dB")

    def calibration_failed(self, idx):
        btn = self.auto_buttons[idx]
        btn.configure(text="CHYBA", fg_color="#ea580c") 
        self.after(2000, lambda: btn.configure(text="[ AUTO ]", fg_color="#4f46e5", hover_color="#4338ca"))
        log_messages.append(f"[KALIBRÁCIA] Zlyhanie: Mic {idx+1} bol príliš tichý na výpočet.")

    def update_mic_slider_label(self, idx, val):
        self.labels_mic[idx].configure(text=f"{float(val):.1f} dB")
        key = ["threshold_mic1", "threshold_mic2", "threshold_mic3", "threshold_mic4"][idx]
        app_settings[key] = round(float(val), 1)

    def create_pacing_slider(self, text, f, t, key, is_int=False, help_key=None):
        frame = ctk.CTkFrame(self.scroll_settings, fg_color="transparent")
        frame.pack(fill="x", padx=10, pady=2)
        
        if help_key:
            btn_h = ctk.CTkButton(frame, text="?", width=20, height=20, corner_radius=10, fg_color="#334155", hover_color="#475569", command=lambda: self.show_help(text, help_key))
            btn_h.pack(side="left", padx=(0, 10))

        ctk.CTkLabel(frame, text=text, width=190, anchor="w", font=ctk.CTkFont(size=12)).pack(side="left")
        
        sl = ctk.CTkSlider(frame, from_=f, to=t, command=lambda v: self.update_pacing_label(lbl, v, is_int, key))
        sl.set(float(app_settings[key]))
        sl.pack(side="left", fill="x", expand=True, padx=10)
        
        display_val = str(int(sl.get())) if is_int else str(round(sl.get(), 1))
        lbl = ctk.CTkLabel(frame, text=display_val, width=40)
        lbl.pack(side="right")
        
        self.pacing_controls[key] = (sl, lbl, is_int)
        return sl, lbl

    def update_pacing_label(self, label_obj, val, is_int, key):
        display_val = str(int(val)) if is_int else str(round(float(val), 1))
        label_obj.configure(text=display_val)
        app_settings[key] = int(val) if is_int else round(float(val), 2)

    def action_save_pacing_settings(self):
        save_settings(app_settings)

    def build_monitor_tab(self):
        self.btn_toggle_ai = ctk.CTkButton(self.tab_monitor, text="ŠTART AI RÉŽIE", fg_color="#10b981", hover_color="#059669", font=ctk.CTkFont(size=18, weight="bold"), height=48, command=self.action_toggle_ai_button)
        self.btn_toggle_ai.pack(fill="x", padx=10, pady=8)

        self.lbl_active_scene = ctk.CTkLabel(self.tab_monitor, text="OBS Scéna: Čakám na pripojenie...", font=ctk.CTkFont(size=14, weight="bold"), text_color="orange")
        self.lbl_active_scene.pack(pady=0)

        frame_diag = ctk.CTkFrame(self.tab_monitor, fg_color="#1e293b", corner_radius=8)
        frame_diag.pack(fill="x", padx=10, pady=5)

        self.lbl_diag_mono = ctk.CTkLabel(frame_diag, text="⏱️ Aktuálny monológ: 0.0 s", font=ctk.CTkFont(weight="bold"))
        self.lbl_diag_mono.grid(row=0, column=0, padx=15, pady=2, sticky="w")

        self.lbl_diag_exch = ctk.CTkLabel(frame_diag, text="🏓 Rýchle výmeny: 0 / 4", font=ctk.CTkFont(weight="bold"))
        self.lbl_diag_exch.grid(row=0, column=1, padx=15, pady=2, sticky="w")

        self.lbl_diag_cool = ctk.CTkLabel(frame_diag, text="🔒 Blokovanie (Lock): 0.0 s", font=ctk.CTkFont(weight="bold"))
        self.lbl_diag_cool.grid(row=1, column=0, padx=15, pady=2, sticky="w")

        self.lbl_diag_stat = ctk.CTkLabel(frame_diag, text="🧠 AI Status: Pripravený", font=ctk.CTkFont(weight="bold"))
        self.lbl_diag_stat.grid(row=1, column=1, padx=15, pady=2, sticky="w")

        self.progress_bars = []
        self.signal_dots = [] 
        names = ["Mic 1 (Host)", "Mic 2 (Guest)", "Mic 3 (Guest Ex)", "Mic 4 (Host Ex)"]
        
        for i in range(4):
            frame = ctk.CTkFrame(self.tab_monitor, fg_color="transparent")
            frame.pack(fill="x", padx=10, pady=1)
            
            dot = ctk.CTkLabel(frame, text="🔴", width=25, font=ctk.CTkFont(size=14))
            dot.pack(side="left")
            self.signal_dots.append(dot)
            
            ctk.CTkLabel(frame, text=names[i], width=100, anchor="w").pack(side="left", padx=(2,0))
            
            pb = ctk.CTkProgressBar(frame, height=12)
            pb.set(0.0)
            pb.pack(side="left", fill="x", expand=True, padx=10)
            self.progress_bars.append(pb)

        lbl_l = ctk.CTkLabel(self.tab_monitor, text="Denník rozhodnutí režiséra (Decision Log)", font=ctk.CTkFont(size=13, weight="bold"))
        lbl_l.pack(anchor="w", padx=10, pady=(5,0))

        self.txt_log = ctk.CTkTextbox(self.tab_monitor, font=ctk.CTkFont(family="Consolas", size=12))
        self.txt_log.pack(fill="both", expand=True, padx=10, pady=5)
        
        log_messages.append("=== AI PODCAST DIRECTOR PRO v2.3 (Master Release) ===")
        log_messages.append(f"Web Remote Server spustený na: http://{LOCAL_IP}:{FLASK_PORT}")

    def build_remote_tab(self):
        container = ctk.CTkFrame(self.tab_remote, fg_color="transparent")
        container.pack(expand=True, fill="both", padx=40, pady=20)

        ctk.CTkLabel(container, text="📱 Studio Web Remote", font=ctk.CTkFont(family="Urbanist", size=28, weight="bold"), text_color="#38bdf8").pack(pady=(0, 10))
        ctk.CTkLabel(container, text="Namier foťák svojho mobilu na tento QR kód.\nMobil a PC musia byť pripojené na rovnakej Wi-Fi sieti.", font=ctk.CTkFont(size=14)).pack(pady=(0, 20))

        self.lbl_qr = ctk.CTkLabel(container, text="")
        self.lbl_qr.pack()
        
        self.lbl_qr_url = ctk.CTkLabel(container, text="", font=ctk.CTkFont(family="Consolas", size=16), text_color="#10b981")
        self.lbl_qr_url.pack(pady=10)
        
        btn_refresh = ctk.CTkButton(container, text="Obnoviť lokálnu sieť (Refresh IP)", fg_color="#4f46e5", hover_color="#4338ca", command=self.action_refresh_qr)
        btn_refresh.pack(pady=10)
        
        self.action_refresh_qr() 

    def action_refresh_qr(self):
        global LOCAL_IP
        LOCAL_IP = get_local_ip()
        try:
            remote_url = f"http://{LOCAL_IP}:{FLASK_PORT}"
            qr_img = qrcode.make(remote_url).get_image()
            ctk_qr = ctk.CTkImage(light_image=qr_img, dark_image=qr_img, size=(220, 220))
            self.lbl_qr.configure(image=ctk_qr)
            self.lbl_qr_url.configure(text=remote_url)
        except Exception as e:
            self.lbl_qr_url.configure(text=f"Chyba: {e}", text_color="red")

    def build_about_tab(self):
        container = ctk.CTkFrame(self.tab_about, fg_color="transparent")
        container.pack(expand=True, fill="both", padx=20, pady=20)

        try:
            url = "https://jakubmrg.sk/wp-content/uploads/2026/04/jmg-for-thumbnail-mic-e1776764309829.png"
            response = requests.get(url, timeout=5)
            img_data = Image.open(io.BytesIO(response.content))
            img_data.thumbnail((200, 200))
            ctk_img = ctk.CTkImage(light_image=img_data, dark_image=img_data, size=(160, 160))
            
            lbl_img = ctk.CTkLabel(container, image=ctk_img, text="")
            lbl_img.pack(side="left", padx=10)
        except Exception:
            lbl_img_fallback = ctk.CTkLabel(container, text="[ Fotografia nedostupná ]", width=160, height=160, fg_color="#1e293b", corner_radius=10)
            lbl_img_fallback.pack(side="left", padx=10)

        text_frame = ctk.CTkFrame(container, fg_color="transparent")
        text_frame.pack(side="left", fill="both", expand=True, padx=20)

        ctk.CTkLabel(text_frame, text="Jakub Mr. G", font=ctk.CTkFont(family="Urbanist", size=30, weight="bold"), text_color="#deff9a").pack(anchor="w", pady=(0, 5))
        
        bio = ("Tvorca podcastu #NEMAMCASNUDITSA a zástanca filozofie Kaizen.\n\n"
               "Svoje dlhoročné skúsenosti z krízového manažmentu a optimalizácie procesov "
               "pretavuje do vývoja nástrojov pre tvorcov obsahu. "
               "Je autorom sebarozvojového konceptu Stroj času – nástroja, ktorý pomáha "
               "dosahovať ciele udržateľným zlepšovaním (Kaizen) a princípmi neuroplasticity.\n\n"
               "Odovzdáva komunite know-how, ako zefektívniť svoju prácu a neustále rásť.\n\n"
               "Vystúp z komfortnej zóny a buď lepší ako včera...")
        
        lbl_bio = ctk.CTkLabel(text_frame, text=bio, font=ctk.CTkFont(size=13), justify="left", wraplength=400)
        lbl_bio.pack(anchor="w")
        
        btn_frame = ctk.CTkFrame(text_frame, fg_color="transparent")
        btn_frame.pack(anchor="w", pady=15, fill="x")
        
        btn_web = ctk.CTkButton(btn_frame, text="Navštíviť oficiálny web", fg_color="#2563eb", hover_color="#1d4ed8", font=ctk.CTkFont(weight="bold"), command=lambda: webbrowser.open("https://www.jakubmrg.sk"))
        btn_web.pack(side="left", padx=(0, 10))
        
        btn_feedback = ctk.CTkButton(btn_frame, text="✉️ Poslať Feedback / Log", fg_color="#f59e0b", hover_color="#d97706", font=ctk.CTkFont(weight="bold"), command=self.action_send_feedback)
        btn_feedback.pack(side="left")

    def action_send_feedback(self):
        log_text = self.txt_log.get("0.0", "end").strip()
        lines = log_text.split('\n')
        recent_logs = "\n".join(lines[-30:])
        
        u_name = app_settings.get("user_name", "Tvorca")
        p_name = app_settings.get("podcast_name", "Podcast")
        
        body = f"Ahoj Jakub,\n\nTu je {u_name} z podcastu '{p_name}'. Posielam feedback na aplikáciu AI Director Pro.\n\n[Miesto pre tvoju správu a popis problému]\n\n---\nDEBUG LOG:\n{recent_logs}"
        subject = "AI Podcast Director Pro - Feedback & Debug Log"
        mailto_link = f"mailto:mrg.golive@gmail.com?subject={urllib.parse.quote(subject)}&body={urllib.parse.quote(body)}"
        try: webbrowser.open(mailto_link)
        except Exception as e: messagebox.showerror("Chyba", f"Nepodarilo sa otvoriť e-mailový klient.\n\nPošli e-mail na mrg.golive@gmail.com")

    def update_gui_loop(self):
        global live_levels, log_messages, active_obs_scene_name, display_levels_db
        global diag_monologue_time, diag_exchange_count, diag_cooldown, diag_state_text, ai_enabled
        
        if ai_enabled:
            self.btn_toggle_ai.configure(text="ZASTAVIŤ AI RÉŽIU (KILL SWITCH)", fg_color="#ef4444", hover_color="#dc2626")
            self.lbl_active_scene.configure(text=f"Aktuálna scéna v OBS: {active_obs_scene_name}", text_color="#10b981")
        else:
            self.btn_toggle_ai.configure(text="ŠTART AI RÉŽIE", fg_color="#10b981", hover_color="#059669")
            self.lbl_active_scene.configure(text=f"Aktuálna scéna v OBS: {active_obs_scene_name} (MANUÁLNY REŽIM)", text_color="#f59e0b")

        self.lbl_diag_mono.configure(text=f"⏱️ Aktuálny monológ: {round(diag_monologue_time, 1)} s")
        self.lbl_diag_exch.configure(text=f"🏓 Rýchle výmeny: {diag_exchange_count} / {app_settings['rapid_exchange_limit']}")
        self.lbl_diag_cool.configure(text=f"🔒 Blokovanie (Lock): {round(diag_cooldown, 1)} s")
        self.lbl_diag_stat.configure(text=f"🧠 AI Status: {diag_state_text}")

        for i in range(4):
            live_lin = live_levels[i]
            if live_lin > 1e-4: live_db = 20 * np.log10(live_lin)
            else: live_db = -60.0
                
            if live_db > -55.0: self.signal_dots[i].configure(text="🟢")
            else: self.signal_dots[i].configure(text="🔴")

            if live_db > display_levels_db[i]: display_levels_db[i] = live_db 
            else: display_levels_db[i] = max(-60.0, display_levels_db[i] - 1.5) 
                
            pb_val = (display_levels_db[i] + 60.0) / 60.0
            self.progress_bars[i].set(max(0.0, min(1.0, pb_val)))
            
            thresh_db = float(app_settings[["threshold_mic1", "threshold_mic2", "threshold_mic3", "threshold_mic4"][i]])
            if display_levels_db[i] > thresh_db: self.progress_bars[i].configure(progress_color="#f97316") 
            else: self.progress_bars[i].configure(progress_color="#3b82f6") 

        if log_messages:
            self.txt_log.configure(state="normal")
            for msg in log_messages:
                self.txt_log.insert("end", msg + "\n")
            self.txt_log.see("end")
            log_messages.clear()
            self.txt_log.configure(state="disabled")

        self.after(50, self.update_gui_loop)

if __name__ == "__main__":
    web_thread = threading.Thread(target=start_flask_server, daemon=True)
    web_thread.start()

    backend_thread = threading.Thread(target=ai_director_backend_thread, daemon=True)
    backend_thread.start()

    app = AIDirectorProGUI()
    app.mainloop()