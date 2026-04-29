"""
daily_nps.py — Streamlit app + headless function that computes a "transit-day"
Net Planetary Strength (NPS) score for each of the 9 planets for any chosen
date+time+timezone, with NO birth chart / lagna involved.

This re-uses the constants and base helper functions from `logic.py` (via the
same exec-without-UI loader used by `logicapi.py`) and re-implements the NPS
pipeline with these differences from the birth-chart pipeline:

   KEEP (sign / degree based, house-independent)
      • Sthanabala-based volume
      • Currency composition (good/bad % per planet, Moon-phase tithi mapping)
      • Mars-in-Leo 75/25 conversion
      • Neechabhangam (co-occupant variant uses SAME-SIGN lookup instead
         of same-house lookup — astrologically identical for this case)
      • Rahu Phase 0 Step 1 (Dispositor-status bonus)
      • Rahu Phase 0 Step 2 (Favourite-sign bonus)
      • Phase 2  (Rasi malefic pull)            — degree-gap only, untouched
      • Phase 2b (Rasi benefic pull)            — degree-gap only, untouched
      • Phase 4  (Gift Pot: Sag/Pis/Lib/Tau)    — sign-based, untouched
      • Phase 5  Virtual Aspect Clones          — to be added in stage 2
      • KHS (ruled-signs)                       — to be added in stage 2
      • Final NPS case formula + predictions normalisation

   DROP (depends on lagna / houses)
      • Lagna / ascendant
      • Navamsa (D9) entire cycle (Phase 1a/1b/1c + Ketu navamsa gift +
         20 % carry-forward)
      • Phase 3 (11th-house gift)
      • Phase 5.1 (House Lord Bonus good-currency add)
      • Phase 5.4 (Suchama / Maraivu reduction)
      • Maraivu-Adjusted NPS column
      • Kendra / Kona sthana boost
      • Rahu Phase 0 Step 3 (Friend-of-Lagna)
      • Digbala — wherever it was a weight, Sthanabala substitutes (no places
         remain in the kept blocks for daily NPS)

Run:
    streamlit run Server/logic/daily_nps.py

Headless:
    from Server.logic.daily_nps import compute_daily_nps
    compute_daily_nps('2026-04-29', '12:00', 'Asia/Kolkata')
"""

from __future__ import annotations

import copy
import json
import os
import sys
from collections import defaultdict
from datetime import datetime, timedelta

import pandas as pd
import pytz

# Swisseph is required
try:
    import swisseph as swe
    USE_SWISSEPH = True
except ImportError:
    swe = None
    USE_SWISSEPH = False

# ──────────────────────────────────────────────────────────────────────
# Constants & Helpers (Extracted from logic.py to make daily_nps standalone)
# ──────────────────────────────────────────────────────────────────────

sign_names = ['Aries','Taurus','Gemini','Cancer','Leo','Virgo','Libra','Scorpio','Sagittarius','Capricorn','Aquarius','Pisces']
sign_lords = ['Mars','Venus','Mercury','Moon','Sun','Mercury','Venus','Mars','Jupiter','Saturn','Saturn','Jupiter']

sthana_bala_dict = {
    'Sun':     [100, 90, 80, 70, 80, 50, 40, 50, 60, 70, 80, 90],
    'Moon':    [ 70,100, 70, 80, 70, 60, 50, 40, 50, 60, 60, 70],
    'Jupiter': [ 60, 60, 60,100, 80, 60, 60, 60, 80, 40, 50, 70],
    'Venus':   [ 60, 70, 60, 50, 40, 30, 80, 50, 60, 70, 60,100],
    'Mercury': [ 40, 60, 80, 50, 70,100, 70, 50, 50, 60, 50, 30],
    'Mars':    [ 80, 70, 60, 40, 60, 60, 60, 60, 70,100, 70, 60],
    'Saturn':  [ 40, 50, 60, 70, 80, 60,100, 90, 60, 80, 90, 50],
    'Rahu':    [100]*12,
    'Ketu':    [100]*12
}

status_data = {
    'Sun': {'Uchcham': 'Aries', 'Moolathirigonam': None, 'Aatchi': 'Leo', 'Neecham': 'Libra'},
    'Moon': {'Uchcham': 'Taurus', 'Moolathirigonam': None, 'Aatchi': 'Cancer', 'Neecham': 'Scorpio'},
    'Jupiter': {'Uchcham': 'Cancer', 'Moolathirigonam': 'Sagittarius', 'Aatchi': 'Pisces', 'Neecham': 'Capricorn'},
    'Venus': {'Uchcham': 'Pisces', 'Moolathirigonam': 'Libra', 'Aatchi': 'Taurus', 'Neecham': 'Virgo'},
    'Mercury': {'Uchcham': 'Virgo', 'Moolathirigonam': None, 'Aatchi': 'Gemini', 'Neecham': 'Pisces'},
    'Mars': {'Uchcham': 'Capricorn', 'Moolathirigonam': 'Aries', 'Aatchi': 'Scorpio', 'Neecham': 'Cancer'},
    'Saturn': {'Uchcham': 'Libra', 'Moolathirigonam': 'Aquarius', 'Aatchi': 'Capricorn', 'Neecham': 'Aries'}
}

capacity_dict = {
    'Saturn': 100, 'Mars': 100, 'Sun': 100, 'Jupiter': 100, 
    'Venus': 50, 'Mercury': 30, 'Moon': 100, 'Rahu': 100, 'Ketu': 50
}
good_capacity_dict = {
    'Saturn': 0, 'Mars': 25, 'Sun': 50, 'Jupiter': 100, 
    'Venus': 100, 'Mercury': 100, 'Rahu': 0, 'Ketu': 0
}
bad_capacity_dict = {
    'Saturn': 100, 'Mars': 75, 'Sun': 50, 'Jupiter': 0, 
    'Venus': 0, 'Mercury': 0, 'Rahu': 100, 'Ketu': 100
}

shukla_good = [100, 9, 16, 23, 30, 37, 44, 51, 58, 65, 72, 79, 86, 93, 100]
shukla_bad = [0] * 15
krishna_good = [93, 86, 79, 72, 65, 58, 51, 44, 37, 30, 23, 16, 9, 2, 0]
krishna_bad = [7, 14, 21, 28, 35, 42, 49, 56, 63, 70, 77, 84, 91, 98, 100]

shukla_tithi_names = ['Shukla Pratipada', 'Shukla Dwitiya', 'Shukla Tritiya', 'Shukla Chaturthi', 'Shukla Panchami', 'Shukla Shashti', 'Shukla Saptami', 'Shukla Ashtami', 'Shukla Navami', 'Shukla Dashami', 'Shukla Ekadashi', 'Shukla Dwadashi', 'Shukla Trayodashi', 'Shukla Chaturdashi', 'Purnima']
krishna_tithi_names = ['Krishna Pratipada', 'Krishna Dwitiya', 'Krishna Tritiya', 'Krishna Chaturthi', 'Krishna Panchami', 'Krishna Shashti', 'Krishna Saptami', 'Krishna Ashtami', 'Krishna Navami', 'Krishna Dashami', 'Krishna Ekadashi', 'Krishna Dwadashi', 'Krishna Trayodashi', 'Krishna Chaturdashi', 'Amavasya']

single_currency_planets = ['Venus', 'Jupiter', 'Mercury', 'Rahu', 'Ketu', 'Saturn']
bad_currency_planets = ['Saturn', 'Rahu', 'Ketu']
malefic_planets = ['Saturn', 'Rahu', 'Ketu', 'Mars', 'Sun']

navamsa_malefic_hierarchy = {'Rahu': 1, 'Sun': 2, 'Saturn': 3, 'Mars': 4, 'Ketu': 5}

mix_dict = {0:100,1:100,2:100,3:95,4:90,5:85,6:80,7:75,8:70,9:65,10:60,11:55,12:50,13:45,14:40,15:35,16:30,17:25,18:20,19:15,20:10,21:5,22:0}

planet_ruled_signs = {
    'Sun': ['Leo'],
    'Moon': ['Cancer'],
    'Mars': ['Aries', 'Scorpio'],
    'Mercury': ['Gemini', 'Virgo'],
    'Jupiter': ['Sagittarius', 'Pisces'],
    'Venus': ['Taurus', 'Libra'],
    'Saturn': ['Capricorn', 'Aquarius']
}

def get_sign(L):
    return sign_names[int(L / 30)]

def get_sign_lord(sign_name):
    try:
        idx = sign_names.index(sign_name)
        return sign_lords[idx]
    except ValueError:
        return None

def is_good_currency(k):
    if k == 'Jupiter Poison': return False
    return 'Good ' in k or k in ['Jupiter', 'Venus', 'Mercury']

def is_sun_or_moon_currency(k):
    return ('Sun' in k) or ('Moon' in k)

PLANET_ORDER = ['Sun', 'Moon', 'Mars', 'Mercury', 'Jupiter', 'Venus',
                'Saturn', 'Rahu', 'Ketu']
LOWER_ORDER  = ['sun', 'moon', 'mars', 'mercury', 'jupiter', 'venus',
                'saturn', 'rahu', 'ketu']


# ──────────────────────────────────────────────────────────────────────
# Main pipeline
# ──────────────────────────────────────────────────────────────────────

def compute_daily_nps(date_str: str, time_str: str = "12:00",
                      tz_name: str = "Asia/Kolkata") -> dict:
    """Compute per-planet NPS scores for the given moment.

    Returns a dict with keys:
        'as_of'         — ISO datetime in UTC
        'tz'            — input timezone name
        'paksha'        — 'Shukla' or 'Krishna'
        'tithi_name'    — e.g. 'Shukla Saptami'
        'planets'       — { planet_name: {... per-planet fields ...} }
    """
    if not USE_SWISSEPH or swe is None:
        raise RuntimeError("Swiss Ephemeris not available — required for daily NPS")

    # ── 1. Parse local datetime → UTC ──────────────────────────────────
    y, mo, d = (int(x) for x in date_str.split('-'))
    hr, mi   = (int(x) for x in time_str.split(':'))
    tz       = pytz.timezone(tz_name)
    local_dt = tz.localize(datetime(y, mo, d, hr, mi, 0))
    utc_dt   = local_dt.astimezone(pytz.utc)

    # ── 2. Sidereal positions (Lahiri) — no lagna needed ──────────────
    swe.set_sid_mode(swe.SIDM_LAHIRI)
    jd = swe.julday(utc_dt.year, utc_dt.month, utc_dt.day,
                    utc_dt.hour + utc_dt.minute / 60.0 + utc_dt.second / 3600.0,
                    swe.GREG_CAL)
    flags = swe.FLG_SIDEREAL | swe.FLG_SWIEPH
    planet_ids = {
        'sun': swe.SUN, 'moon': swe.MOON, 'mercury': swe.MERCURY,
        'venus': swe.VENUS, 'mars': swe.MARS, 'jupiter': swe.JUPITER,
        'saturn': swe.SATURN, 'rahu': swe.MEAN_NODE,
    }
    lon_sid = {}
    for name, pid in planet_ids.items():
        result, _flag = swe.calc_ut(jd, pid, flags)
        lon_sid[name] = result[0]
    lon_sid['ketu'] = (lon_sid['rahu'] + 180.0) % 360.0

    # ── 3. Tithi + Paksha (Sun/Moon angular separation) ────────────────
    sun_lon  = lon_sid['sun']
    moon_lon = lon_sid['moon']
    moon_sun_diff = (moon_lon - sun_lon) % 360
    tithi_full = moon_sun_diff / 12.0
    tithi_idx_full = int(tithi_full)
    if tithi_idx_full >= 30:
        tithi_idx_full = 29
    paksha = 'Shukla' if tithi_idx_full < 15 else 'Krishna'
    tithi_idx = tithi_idx_full if paksha == 'Shukla' else tithi_idx_full - 15
    moon_phase_name = (shukla_tithi_names[tithi_idx] if paksha == 'Shukla'
                       else krishna_tithi_names[tithi_idx])

    # ── 4. Sign + status maps ─────────────────────────────────────────
    planet_sign_map   = {}
    planet_status_map = {}
    for p in LOWER_ORDER:
        L = lon_sid[p]
        sign = get_sign(L)
        cap = p.capitalize()
        planet_sign_map[cap] = sign
        status = '-'
        if cap in status_data:
            m = status_data[cap]
            if   sign == m['Uchcham']:        status = 'Uchcham'
            elif sign == m['Neecham']:        status = 'Neecham'
            elif sign == m['Moolathirigonam']: status = 'Moolathirigonam'
            elif sign == m['Aatchi']:         status = 'Aatchi'
        planet_status_map[cap] = status

    # Uchcham-ruled signs (volume +10% boost — pure sign logic, kept)
    uchcham_ruled_signs = set()
    for cap, st in planet_status_map.items():
        if st == 'Uchcham' and cap in planet_ruled_signs:
            for rsg in planet_ruled_signs[cap]:
                uchcham_ruled_signs.add(rsg)

    # Parivardhana (mutual sign-lord exchange) — sign-based, kept
    parivardhana_map = {}
    for pa in ['Sun', 'Moon', 'Mars', 'Mercury', 'Jupiter', 'Venus', 'Saturn']:
        sg_a = planet_sign_map[pa]
        lord_a = get_sign_lord(sg_a)
        if lord_a in planet_sign_map:
            sg_lord = planet_sign_map[lord_a]
            lord_of_that = get_sign_lord(sg_lord)
            if lord_of_that == pa and pa != lord_a:
                parivardhana_map[pa] = lord_a

    # ── 5. Initial inventories (Phase 0) ───────────────────────────────
    moon_initial_good_val = 0.0
    planet_data = {}
    for p in LOWER_ORDER:
        L = lon_sid[p]
        sign = get_sign(L)
        cap = p.capitalize()
        
        # Apply Parivartana Sthana swap if active
        if cap in parivardhana_map:
            exchange_lord = parivardhana_map[cap]
            exchange_sign = planet_sign_map[exchange_lord]
            sthana = sthana_bala_dict.get(cap, [0]*12)[sign_names.index(exchange_sign)]
        else:
            sthana = sthana_bala_dict.get(cap, [0]*12)[sign_names.index(sign)]
            
        # NOTE: Kendra/Kona sthana boost SKIPPED for daily NPS
        capacity = capacity_dict.get(cap, None)
        volume = (capacity * sthana / 100.0) if capacity is not None else 0.0
        if sign in uchcham_ruled_signs:
            volume *= 1.10
        status = planet_status_map[cap]

        # Currency composition
        moon_good_pct = 0
        moon_bad_pct  = 0
        if cap == 'Moon':
            if paksha == 'Shukla':
                good_pct = shukla_good[tithi_idx]
                bad_pct  = shukla_bad[tithi_idx]
            else:
                good_pct = krishna_good[tithi_idx]
                bad_pct  = krishna_bad[tithi_idx]
            # Amavasya combust override
            sep = (moon_lon - sun_lon) % 360
            if sep >= 348 or sep < 12:
                good_pct, bad_pct = 0, 100
            moon_good_pct, moon_bad_pct = good_pct, bad_pct
        else:
            good_pct = good_capacity_dict.get(cap, 0)
            bad_pct  = bad_capacity_dict.get(cap, 0)

        good_val = volume * good_pct / 100.0
        bad_val  = volume * bad_pct  / 100.0
        if cap == 'Moon':
            moon_initial_good_val = good_val

        # Neechabhangam handling — same as logic.py but co-occupant check
        # uses SAME-SIGN instead of same-house (functionally identical:
        # one sign = one house in any chart).
        total_debt = 0.0
        has_debt = False
        updated_status = '-'
        is_neechabhangam = False
        is_healthy_neecham_moon = False
        nb_good_add = 0.0
        nb_bad_add  = 0.0
        if status == 'Neecham':
            if cap == 'Moon' and paksha == 'Shukla' and bad_val == 0:
                is_healthy_neecham_moon = True
            house_lord = get_sign_lord(sign)
            hl_status  = planet_status_map.get(house_lord, '-')
            if hl_status in ['Uchcham', 'Moolathirigonam', 'Aatchi']:
                updated_status = 'Neechabhangam'
                is_neechabhangam = True
                nb_base_vol = capacity * 0.40
                if cap in ['Saturn', 'Mars']:
                    nb_good_add = nb_base_vol
                    nb_bad_add  = 0.0
                else:
                    nb_good_add = nb_base_vol * good_pct / 100.0
                    nb_bad_add  = nb_base_vol * bad_pct  / 100.0
                good_val += nb_good_add
                bad_val  += nb_bad_add
            else:
                # Co-occupant check via SAME SIGN (was same-house in logic.py)
                cur_sign = sign
                for other in PLANET_ORDER:
                    if other == cap:
                        continue
                    if planet_sign_map.get(other) == cur_sign:
                        ostat = planet_status_map.get(other, '-')
                        if ostat in ['Uchcham', 'Moolathirigonam']:
                            updated_status = 'Neechabhangam'
                            is_neechabhangam = True
                            break
            if is_healthy_neecham_moon:
                if capacity is not None:
                    good_capacity = capacity * good_pct / 100.0
                    total_debt = -((1.2 * good_capacity) - good_val)
                    has_debt = True
            else:
                if capacity is not None:
                    total_debt = -((1.2 * capacity) - good_val)
                    has_debt = True
            if is_neechabhangam and cap in ['Saturn', 'Mars']:
                total_debt += nb_good_add
        else:
            if bad_val > 0:
                total_debt = -bad_val
                has_debt = True

        planet_data[cap] = {
            'sthana': sthana, 'volume': volume,
            'L': L, 'sign': sign, 'status': status,
            'updated_status': updated_status,
            'parivardhana': parivardhana_map.get(cap, '-'),
            'good_inv': good_val, 'bad_inv': bad_val,
            'current_debt': total_debt,
            'final_inventory': defaultdict(float),
            'moon_phase': moon_phase_name if cap == 'Moon' else None,
            'moon_bad_pct': moon_bad_pct if cap == 'Moon' else 0,
            'moon_good_pct': moon_good_pct if cap == 'Moon' else 0,
        }

        # Seed inventory (mirrors logic.py)
        inv = planet_data[cap]['final_inventory']
        if cap in ['Jupiter', 'Venus', 'Mercury']:
            if good_val > 0: inv[cap] = good_val
        elif cap in ['Saturn', 'Rahu']:
            if is_neechabhangam and good_val > 0:
                inv[f"Good {cap}"] = good_val
            if bad_val > 0: inv[f"Bad {cap}"] = bad_val
        elif cap == 'Ketu':
            if good_val > 0: inv[f"Good {cap}"] = good_val
            if bad_val > 0: inv[f"Bad {cap}"] = bad_val
        else:  # Sun, Moon, Mars
            if good_val > 0: inv[f"Good {cap}"] = good_val
            if bad_val > 0: inv[f"Bad {cap}"] = bad_val

    # Mars-in-Leo 75/25 (sign-based, kept)
    if planet_data['Mars']['sign'] == 'Leo':
        inv = planet_data['Mars']['final_inventory']
        gv = inv.get('Good Mars', 0.0)
        bv = inv.get('Bad Mars', 0.0)
        tot = gv + bv
        ng = tot * 0.75
        nb = tot * 0.25
        inv['Good Mars'] = ng
        inv['Bad Mars']  = nb
        planet_data['Mars']['current_debt'] = -nb

    # ── 6. Rahu Phase 0 (modified — Friend-of-Lagna SKIPPED) ──────────
    rahu_sign = planet_sign_map.get('Rahu', 'Aries')
    rahu_disp = get_sign_lord(rahu_sign)
    rahu_disp_status = planet_status_map.get(rahu_disp, '-')
    # Step 1: dispositor status
    step1 = {'Uchcham': 80, 'Moolathirigonam': 48, 'Aatchi': 36}.get(rahu_disp_status, 0)
    if step1:
        planet_data['Rahu']['final_inventory']['Good Rahu'] = (
            planet_data['Rahu']['final_inventory'].get('Good Rahu', 0.0) + step1)
        planet_data['Rahu']['current_debt'] += step1
    # Step 2: favourite-sign bonus
    fav_signs = {'Aries', 'Taurus', 'Cancer', 'Virgo', 'Capricorn'}
    step2 = 30 if rahu_sign in fav_signs else 0
    if step2:
        planet_data['Rahu']['final_inventory']['Good Rahu'] = (
            planet_data['Rahu']['final_inventory'].get('Good Rahu', 0.0) + step2)
        planet_data['Rahu']['current_debt'] += step2
    # Step 3 (Friend-of-Lagna) DROPPED.

    # Snapshot — END OF PHASE 0 (initial inventories + Rahu Phase-0)
    _snap_phase0 = {
        p: {
            'inventory': dict(planet_data[p]['final_inventory']),
            'debt': planet_data[p]['current_debt'],
        } for p in PLANET_ORDER
    }

    # ── 7. Phase 2 (Rasi malefic+benefic pull) ─────────────────────────
    # The original Phase 1 ("Rasi Phase 1" malefic pull) in logic.py is
    # already pure degree-gap based (22° cap via mix_dict) — no house
    # references. We port it verbatim.
    is_waxing = (paksha == 'Shukla') or (moon_phase_name == 'Purnima')
    is_waning = not is_waxing
    bad_pct_moon = planet_data['Moon']['moon_bad_pct']
    moon_in_list = False
    debtor_rank = ['Rahu', 'Sun', 'Saturn']
    if moon_phase_name == 'Amavasya':
        debtor_rank.append('Moon')
        moon_in_list = True
    debtor_rank.append('Mars')
    if is_waning and not moon_in_list:
        debtor_rank.append('Moon')
    debtor_rank.append('Ketu')

    def get_currency_rank_score(p_name, c_key):
        if p_name == 'Moon':
            phase = planet_data['Moon']['moon_phase']
            is_shukla = (paksha == 'Shukla')
            idx = tithi_idx
            if phase == 'Purnima': return 1000
            if 'Good' in c_key or c_key == 'Moon':
                pct = shukla_good[idx] if is_shukla else krishna_good[idx]
                return 500 + pct * 4
        if c_key == 'Jupiter':  return 990
        if c_key == 'Venus':    return 980
        if c_key == 'Mercury':  return 970
        if c_key == 'Good Mars': return 800
        if c_key == 'Good Sun':  return 700
        if c_key == 'Good Ketu': return 700
        if c_key == 'Good Rahu': return 100
        if p_name == 'Moon' and 'Bad' in c_key:
            pct = planet_data['Moon']['moon_bad_pct']
            return 400 - pct * 3
        if c_key == 'Bad Mars':   return 325
        if c_key == 'Bad Sun':    return 250
        if c_key == 'Bad Saturn': return 100
        if c_key == 'Bad Rahu':   return 100
        if c_key == 'Bad Ketu':   return 150
        return 0

    loop_active = True
    cycles = 0
    while loop_active and cycles < 200:
        cycles += 1
        something = False
        for debtor in debtor_rank:
            if planet_data[debtor]['current_debt'] >= -0.001:
                continue
            d_is_mal = debtor in malefic_planets
            d_rank   = navamsa_malefic_hierarchy.get(debtor, 99)
            potentials = []
            for t in PLANET_ORDER:
                if t == debtor:
                    continue
                if debtor == 'Ketu' and t not in ['Sun', 'Moon']:
                    continue
                t_is_mal = t in malefic_planets
                if d_is_mal and t_is_mal:
                    if d_rank >= navamsa_malefic_hierarchy.get(t, 99):
                        continue
                else:
                    di = debtor_rank.index(debtor) if debtor in debtor_rank else 99
                    ti = debtor_rank.index(t)      if t      in debtor_rank else 99
                    if di > ti:
                        continue
                inv = planet_data[t]['final_inventory']
                for key, val in inv.items():
                    if key == 'Good Rahu':
                        continue
                    if 'Bad' in key and key != f"Bad {t}":
                        continue
                    if val > 0.001:
                        L1 = planet_data[debtor]['L']
                        L2 = planet_data[t]['L']
                        diff = abs(L1 - L2)
                        if diff > 180:
                            diff = 360 - diff
                        gap = int(diff)
                        if gap > 22:
                            continue
                        cap_pct = mix_dict.get(gap, 0)
                        max_pull = planet_data[t]['volume'] * cap_pct / 100.0
                        tk = f"pulled_from_{t}"
                        already = planet_data[debtor].get(tk, 0.0)
                        if already < max_pull:
                            score = get_currency_rank_score(t, key)
                            potentials.append({
                                'planet': t, 'key': key, 'score': score,
                                'gap': gap, 'max_pull': max_pull,
                                'is_good': is_good_currency(key),
                            })
            if d_is_mal:
                potentials.sort(key=lambda x: (-int(x['is_good']), -x['score'], x['gap']))
            else:
                potentials.sort(key=lambda x: (-x['score'], x['gap']))
            good_avail = any(t['is_good'] and
                             planet_data[t['planet']]['final_inventory'].get(t['key'], 0) > 0
                             for t in potentials)
            for tg in potentials:
                if planet_data[debtor]['current_debt'] >= -0.001:
                    break
                own_bad = f"Bad {debtor}" if debtor != 'Moon' else "Bad Moon"
                if tg['key'] == own_bad:
                    continue
                if debtor == 'Sun' and tg['key'] == 'Bad Moon':
                    continue
                if d_is_mal and not tg['is_good'] and good_avail:
                    continue
                avail = planet_data[tg['planet']]['final_inventory'][tg['key']]
                if avail <= 0:
                    continue
                tk = f"pulled_from_{tg['planet']}"
                already = planet_data[debtor].get(tk, 0.0)
                cap_space = tg['max_pull'] - already
                if cap_space <= 0:
                    continue
                take = min(1.0, avail, cap_space)
                if take <= 0:
                    continue
                planet_data[tg['planet']]['final_inventory'][tg['key']] -= take
                planet_data[tg['planet']]['current_debt']               -= take
                is_ketu_curr = tg['key'] in ('Bad Ketu', 'Good Ketu')
                is_sm = debtor in ('Sun', 'Moon')
                if is_ketu_curr and not is_sm:
                    planet_data[debtor]['final_inventory']['Good Ketu'] += take
                    planet_data[debtor]['current_debt']                 += take
                elif debtor in ('Rahu', 'Sun') and tg['planet'] == 'Saturn' and tg['key'] == 'Good Saturn':
                    planet_data[debtor]['final_inventory']['Bad Saturn'] += take
                    planet_data[debtor]['current_debt']                  -= take
                else:
                    planet_data[debtor]['final_inventory'][tg['key']] += take
                    is_bad_flag = ('Bad' in tg['key']) or tg['key'] in ('Amavasya', 'Bad Saturn', 'Bad Rahu')
                    if tg['planet'] in ('Saturn', 'Rahu') and 'Bad' in tg['key']: is_bad_flag = True
                    if tg['planet'] == 'Moon' and 'Bad' in tg['key']: is_bad_flag = True
                    if debtor == 'Ketu' and is_sun_or_moon_currency(tg['key']):
                        planet_data[debtor]['current_debt'] -= take
                    elif is_bad_flag:
                        planet_data[debtor]['current_debt'] -= take
                    else:
                        planet_data[debtor]['current_debt'] += take
                planet_data[debtor][tk] = already + take
                something = True
                # Infection penalty
                tg_is_mal = (tg['planet'] in malefic_planets) or (
                    tg['planet'] == 'Moon' and planet_data['Moon'].get('moon_bad_pct', 0) > 0)
                if d_is_mal and tg_is_mal:
                    inf_key = f"Bad {debtor}" if debtor != 'Moon' else "Bad Moon"
                    planet_data[tg['planet']]['final_inventory'][inf_key] += take
                good_avail = any(t['is_good'] and
                                 planet_data[t['planet']]['final_inventory'].get(t['key'], 0) > 0
                                 for t in potentials)
        if not something:
            loop_active = False

    # ── 8. Phase 2b (Rasi benefic redistribution) ──────────────────────
    moon_is_benefic_p2 = (paksha == 'Shukla') or (moon_phase_name == 'Purnima')
    core_benefics_p2 = ['Jupiter', 'Venus', 'Mercury']
    if moon_is_benefic_p2:
        core_benefics_p2.append('Moon')

    # Snapshot — END OF PHASE 2 (malefic pull only, before benefic redistribution)
    _snap_phase2 = {
        p: {
            'inventory': dict(planet_data[p]['final_inventory']),
            'debt': planet_data[p]['current_debt'],
        } for p in PLANET_ORDER
    }

    phase2_data = {}
    for p in PLANET_ORDER:
        phase2_data[p] = {
            'p2_inventory': defaultdict(float),
            'p2_current_debt': planet_data[p]['current_debt'],
            'volume': planet_data[p]['volume'],
            'L': planet_data[p]['L'],
        }
        for k, v in planet_data[p]['final_inventory'].items():
            phase2_data[p]['p2_inventory'][k] = v

    # Ketu Bad → Good promotion if Ketu has no Sun/Moon currency
    ketu_has_sm = any(is_sun_or_moon_currency(k) and v > 0.001
                      for k, v in phase2_data['Ketu']['p2_inventory'].items())
    bad_ketu_rem = phase2_data['Ketu']['p2_inventory'].get('Bad Ketu', 0.0)
    if bad_ketu_rem > 0 and not ketu_has_sm:
        phase2_data['Ketu']['p2_inventory']['Good Ketu'] = (
            phase2_data['Ketu']['p2_inventory'].get('Good Ketu', 0.0) + bad_ketu_rem)
        phase2_data['Ketu']['p2_inventory']['Bad Ketu'] = 0.0
        phase2_data['Ketu']['p2_current_debt'] += bad_ketu_rem
    if not ketu_has_sm:
        core_benefics_p2.append('Ketu')

    benefic_debt_pct = {}
    for p in core_benefics_p2:
        vol = phase2_data[p]['volume']
        dbt = abs(phase2_data[p]['p2_current_debt'])
        benefic_debt_pct[p] = (dbt / vol * 100) if vol > 0 else 0.0
    sorted_benefics = sorted(core_benefics_p2, key=lambda x: -benefic_debt_pct[x])

    def get_p2_currency_rank_score(_p, ck):
        if ck == 'Jupiter':   return 1000
        if ck == 'Good Moon': return 995
        if ck == 'Venus':     return 980
        if ck == 'Mercury':   return 970
        if ck == 'Good Ketu': return 700
        return 0

    p2_active = True
    p2_cycles = 0
    while p2_active and p2_cycles < 200:
        p2_cycles += 1
        p2_something = False
        for puller in sorted_benefics:
            if phase2_data[puller]['p2_current_debt'] >= -0.001:
                continue
            puller_pct = benefic_debt_pct[puller]
            potentials = []
            for tgt in core_benefics_p2:
                if tgt == puller: continue
                if puller == 'Ketu' and tgt == 'Moon': continue
                if puller == 'Moon' and tgt == 'Ketu': continue
                if benefic_debt_pct[tgt] >= puller_pct: continue
                L1 = phase2_data[puller]['L']
                L2 = phase2_data[tgt]['L']
                diff = abs(L1 - L2)
                if diff > 180: diff = 360 - diff
                gap = int(diff)
                if gap > 22: continue
                inv = phase2_data[tgt]['p2_inventory']
                for key, val in inv.items():
                    if key == 'Good Rahu': continue
                    if 'Bad' in key: continue
                    if val > 0.001:
                        cap_pct = mix_dict.get(gap, 0)
                        max_pull = phase2_data[tgt]['volume'] * cap_pct / 100.0
                        tk = f"p2_pulled_from_{tgt}"
                        already = phase2_data[puller].get(tk, 0.0)
                        if already < max_pull:
                            potentials.append({
                                'planet': tgt, 'key': key, 'score': get_p2_currency_rank_score(tgt, key),
                                'gap': gap, 'max_pull': max_pull,
                            })
            potentials.sort(key=lambda x: (-x['score'], x['gap']))
            for tg in potentials:
                if phase2_data[puller]['p2_current_debt'] >= -0.001:
                    break
                avail = phase2_data[tg['planet']]['p2_inventory'][tg['key']]
                if avail <= 0:
                    continue
                tk = f"p2_pulled_from_{tg['planet']}"
                already = phase2_data[puller].get(tk, 0.0)
                cap_space = tg['max_pull'] - already
                if cap_space <= 0:
                    continue
                take = min(1.0, avail, cap_space)
                if take <= 0:
                    continue
                phase2_data[tg['planet']]['p2_inventory'][tg['key']] -= take
                phase2_data[tg['planet']]['p2_current_debt']         -= take
                phase2_data[puller]['p2_inventory'][tg['key']]        += take
                phase2_data[puller]['p2_current_debt']                += take
                phase2_data[puller][tk] = already + take
                p2_something = True
                for ben in core_benefics_p2:
                    vol = phase2_data[ben]['volume']
                    dbt = abs(phase2_data[ben]['p2_current_debt'])
                    benefic_debt_pct[ben] = (dbt / vol * 100) if vol > 0 else 0.0
        if not p2_something:
            p2_active = False

    # ── 9. Phase 4 (Gift Pots: Sag/Pis/Lib/Tau) — sign-based, kept ──────
    # Carry phase2_data → phase4_data (we skip Phase 3 entirely).

    # Snapshot — END OF PHASE 2b (benefic redistribution)
    _snap_phase2b = {
        p: {
            'inventory': dict(phase2_data[p]['p2_inventory']),
            'debt': phase2_data[p]['p2_current_debt'],
        } for p in PLANET_ORDER
    }

    phase4_data = {}
    for p in PLANET_ORDER:
        phase4_data[p] = {
            'p4_inventory': defaultdict(float, phase2_data[p]['p2_inventory']),
            'p4_current_debt': phase2_data[p]['p2_current_debt'],
            'volume': phase2_data[p]['volume'],
            'L': phase2_data[p]['L'],
        }

    # Pot configuration (multiplier × gifter_sthana / 100, debt cap %)
    gift_cfg = {
        'Sagittarius': {'gifter': 'Jupiter', 'mult': 100, 'cap': 1.00, 'curr': 'Jupiter'},
        'Pisces':      {'gifter': 'Jupiter', 'mult': 80,  'cap': 0.80, 'curr': 'Jupiter'},
        'Libra':       {'gifter': 'Venus',   'mult': 80,  'cap': 0.80, 'curr': 'Venus'},
        'Taurus':      {'gifter': 'Venus',   'mult': 60,  'cap': 0.60, 'curr': 'Venus'},
    }
    initial_p4_debt = {p: phase4_data[p]['p4_current_debt'] for p in PLANET_ORDER}
    # Track unused gift-pot remainder per sign (used by KHS occupant scoring)
    phase4_pot_initial = {}
    phase4_pot_remaining = {}

    for sign_target, cfg in gift_cfg.items():
        gifter = cfg['gifter']
        gifter_sthana = planet_data[gifter]['sthana']
        pot = cfg['mult'] * gifter_sthana / 100.0
        phase4_pot_initial[sign_target] = pot
        phase4_pot_remaining[sign_target] = pot
        if pot <= 0:
            continue
        recipients = [p for p in PLANET_ORDER if planet_sign_map[p] == sign_target]
        if not recipients:
            continue
        debt_cap_pct = cfg['cap']
        # Phase A: malefic debts (rank order)
        mal_recipients = [p for p in recipients if p in malefic_planets]
        mal_recipients.sort(key=lambda x: navamsa_malefic_hierarchy.get(x, 99))
        for m in mal_recipients:
            init_d = abs(initial_p4_debt[m])
            cap_amt = init_d * debt_cap_pct
            given = 0.0
            while pot > 0.001 and phase4_data[m]['p4_current_debt'] < -0.001 and given < cap_amt:
                need = abs(phase4_data[m]['p4_current_debt'])
                take = min(1.0, need, pot, cap_amt - given)
                if take <= 0:
                    break
                phase4_data[m]['p4_inventory'][cfg['curr']] += take
                phase4_data[m]['p4_current_debt']           += take
                pot   -= take
                given += take
        if pot <= 0.001:
            phase4_pot_remaining[sign_target] = pot
            continue
        # Phase B: benefic debts (highest debt%)
        ben_recipients = [p for p in recipients if p not in malefic_planets]
        ben_recipients.sort(key=lambda x: -(abs(phase4_data[x]['p4_current_debt']) /
                                            phase4_data[x]['volume'] * 100
                                            if phase4_data[x]['volume'] > 0 else 0))
        for b in ben_recipients:
            init_d = abs(initial_p4_debt[b])
            cap_amt = init_d * debt_cap_pct
            given = 0.0
            while pot > 0.001 and phase4_data[b]['p4_current_debt'] < -0.001 and given < cap_amt:
                need = abs(phase4_data[b]['p4_current_debt'])
                take = min(1.0, need, pot, cap_amt - given)
                if take <= 0:
                    break
                phase4_data[b]['p4_inventory'][cfg['curr']] += take
                phase4_data[b]['p4_current_debt']           += take
                pot   -= take
                given += take
        phase4_pot_remaining[sign_target] = pot

    # ── 10. Phase 5 — Virtual Aspect Clones, Jupiter Poison, KHS ──────
    # Mirrors logic.py's Phase 5 with these omissions for daily NPS:
    #   • House Lord Bonus (5.1) — DROPPED (uses houses)
    #   • Suchama / Maraivu     — DROPPED (uses houses)
    #   • Lagna-lord HPS adjustments — DROPPED
    #   • Kendraadhibathya / Kona Dosha — DROPPED (need lagna)
    # Everything else (clone creation, Jupiter Poison, interaction cycle,
    # XSUN Saturn absorption, Sun healing, Ketu-alone check, KHS scoring)
    # is degree- or sign-based and is preserved.

    # Snapshot — END OF PHASE 4 (gift pots)
    _snap_phase4 = {
        p: {
            'inventory': dict(phase4_data[p]['p4_inventory']),
            'debt': phase4_data[p]['p4_current_debt'],
        } for p in PLANET_ORDER
    }

    # 10.1 Initialise phase5_data from phase4_data
    phase5_data = {}
    for p in PLANET_ORDER:
        phase5_data[p] = {
            'p5_inventory': defaultdict(float),
            'p5_current_debt': phase4_data[p]['p4_current_debt'],
            'volume': phase4_data[p]['volume'],
            'L': phase4_data[p]['L'],
            'sign': planet_sign_map[p],
            'bad_inv': 0.0,
        }
        for k, v in phase4_data[p]['p4_inventory'].items():
            phase5_data[p]['p5_inventory'][k] = v
            if 'Bad' in k:
                phase5_data[p]['bad_inv'] += v

    # 10.2 Ketu's Rasi gift to Mercury / Venus / Jupiter (degree-based)
    _kg_ketu_L = phase5_data['Ketu']['L']
    _kg_ketu_vol = phase5_data['Ketu']['volume']
    for _kg_ben in ('Mercury', 'Venus', 'Jupiter'):
        _kg_diff = abs(phase5_data[_kg_ben]['L'] - _kg_ketu_L)
        if _kg_diff > 180:
            _kg_diff = 360 - _kg_diff
        _kg_gap = int(_kg_diff)
        if _kg_gap > 22:
            continue
        _kg_pct = mix_dict.get(_kg_gap, 0)
        if _kg_pct <= 0:
            continue
        _kg_gift = _kg_ketu_vol * (_kg_pct / 100.0)
        phase5_data[_kg_ben]['p5_inventory'][_kg_ben] += _kg_gift
        phase5_data[_kg_ben]['p5_current_debt']       += _kg_gift

    # 10.3 Snapshot before any exchanges (clones see same baseline)
    _p5_snapshot_inv  = {sp: dict(phase5_data[sp]['p5_inventory']) for sp in PLANET_ORDER}
    _p5_snapshot_debt = {sp: phase5_data[sp]['p5_current_debt']    for sp in PLANET_ORDER}

    P5_BENEFICS = ['Jupiter', 'Venus', 'Mercury']
    ASPECT_RULES = {
        'Saturn':  {3: 0.25, 7: 1.0, 10: 0.75},
        'Mars':    {4: 0.40, 7: 1.0, 8: 0.25},
        'Sun':     {7: 0.50},
        'Jupiter': {5: 1.0, 7: 1.0, 9: 1.0},
        'Venus':   {7: 1.0},
        'Mercury': {7: 1.0},
        'Moon':    {4: 0.25, 6: 0.50, 7: 1.0, 8: 0.50, 10: 0.25},
    }
    _sun_is_aquarius = (planet_sign_map.get('Sun') == 'Aquarius')
    P5_MAL_DEBTOR_RANK = ['Rahu', 'Sun', 'Saturn', 'Mars', 'Ketu']
    PLANET_SEQUENCE = ['Saturn', 'Mars', 'Sun', 'Jupiter', 'Venus', 'Mercury', 'Moon']

    def _get_p5_currency_rank_score(c_key):
        if c_key in ('Jupiter', 'Jupiter Poison'): return 990
        if c_key == 'Venus':       return 980
        if c_key == 'Mercury':     return 970
        if c_key == 'Good Moon':   return 950
        if c_key == 'Good Saturn': return 780
        if c_key == 'Good Mars':   return 770
        if c_key == 'Good Sun':    return 760
        if c_key == 'Good Ketu':   return 700
        if c_key == 'Bad Moon':    return 300
        if c_key == 'Bad Mars':    return 250
        if c_key == 'Bad Sun':     return 200
        if c_key == 'Bad Saturn':  return 100
        if c_key == 'Bad Rahu':    return 100
        if c_key == 'Bad Ketu':    return 150
        return 0

    def _is_moon_malefic_p5():
        return phase5_data['Moon']['bad_inv'] > 0.001

    _all_planet_clones = {}
    _all_leftover_clones = []

    # 10.4 Clone creation (PASS 1, simultaneous, from snapshot)
    _neg_statuses = ('Neecham', 'Neechabhangam', 'Neechabhanga Raja Yoga')
    for cp in PLANET_SEQUENCE:
        if cp not in ASPECT_RULES:
            continue
        parent_L = phase5_data[cp]['L']
        parent_inv  = _p5_snapshot_inv[cp]
        parent_debt = _p5_snapshot_debt[cp]
        cp_status_raw = planet_data[cp].get('updated_status', '-')
        cp_status = cp_status_raw if cp_status_raw not in ('-', '', None) else planet_data[cp].get('status', '')
        cp_is_malefic = (cp in malefic_planets) or (cp == 'Moon' and phase5_data['Moon']['bad_inv'] > 0.001)
        if cp_is_malefic and cp_status in _neg_statuses:
            scaling = planet_data[cp]['sthana'] / 120.0
        else:
            scaling = 1.0

        clones = []
        for offset, asp_pct in ASPECT_RULES[cp].items():
            clone_L = (parent_L + (offset - 1) * 30) % 360
            clone_inv  = defaultdict(float)
            clone_debt = 0.0
            clone_type = 'Passive'
            is_xsun = False

            if cp == 'Saturn':
                good_sum = sum(v / 2.0 for k, v in parent_inv.items() if is_good_currency(k) and v > 0.001)
                cv = asp_pct * good_sum * scaling
                if cv > 0.001:
                    clone_inv['Good Saturn'] = cv
                for k, v in parent_inv.items():
                    if 'Bad' in k and v > 0.001:
                        bv = v * asp_pct * scaling
                        if bv > 0.001:
                            clone_inv[k] = bv
                if cp_status in _neg_statuses:
                    g = sum(v for k, v in parent_inv.items() if is_good_currency(k) and v > 0.001)
                    b = sum(v for k, v in parent_inv.items() if 'Bad' in k and v > 0.001)
                    clone_debt = (g - b) * asp_pct * scaling
                else:
                    clone_debt = parent_debt * asp_pct * scaling
                clone_type = 'Active'

            elif cp == 'Mars':
                good_sum = 0.0
                for k, v in parent_inv.items():
                    if is_good_currency(k) and v > 0.001:
                        good_sum += v if k == 'Good Mars' else v / 2.0
                cv = asp_pct * good_sum * scaling
                if cv > 0.001:
                    clone_inv['Good Mars'] = cv
                for k, v in parent_inv.items():
                    if 'Bad' in k and v > 0.001:
                        bv = v * asp_pct * scaling
                        if bv > 0.001:
                            clone_inv[k] = bv
                if cp_status in _neg_statuses:
                    g = sum(v for k, v in parent_inv.items() if is_good_currency(k) and v > 0.001)
                    b = sum(v for k, v in parent_inv.items() if 'Bad' in k and v > 0.001)
                    clone_debt = (g - b) * asp_pct * scaling
                else:
                    clone_debt = parent_debt * asp_pct * scaling
                clone_type = 'Active'

            elif cp == 'Sun':
                if _sun_is_aquarius:
                    good_sum = 0.0
                    for k, v in parent_inv.items():
                        if is_good_currency(k) and v > 0.001:
                            good_sum += v if k == 'Good Sun' else v / 2.0
                    cv = asp_pct * good_sum * scaling
                    if cv > 0.001:
                        clone_inv['Good Sun'] = cv
                    for k, v in parent_inv.items():
                        if 'Bad' in k and v > 0.001:
                            bv = v * asp_pct * scaling
                            if bv > 0.001:
                                clone_inv[k] = bv
                    if cp_status in _neg_statuses:
                        g = sum(v for k, v in parent_inv.items() if is_good_currency(k) and v > 0.001)
                        b = sum(v for k, v in parent_inv.items() if 'Bad' in k and v > 0.001)
                        clone_debt = (g - b) * asp_pct * scaling
                    else:
                        clone_debt = parent_debt * asp_pct * scaling
                    clone_type = 'Active'
                else:
                    # XSUN — Passive carrying only Bad Sun (Saturn absorbs)
                    xb = sum(v for k, v in parent_inv.items() if 'Bad' in k and v > 0.001)
                    xv = xb * asp_pct * scaling
                    if xv > 0.001:
                        clone_inv['Bad Sun'] = xv
                    clone_debt = 0.0
                    clone_type = 'Passive'
                    is_xsun = True

            elif cp in P5_BENEFICS:
                good_sum = sum(v for k, v in parent_inv.items() if is_good_currency(k) and v > 0.001)
                cv = asp_pct * good_sum * scaling
                if cv > 0.001:
                    clone_inv[cp] = cv
                clone_debt = 0.0
                clone_type = 'Passive'

            elif cp == 'Moon':
                good_moon_val = parent_inv.get('Good Moon', 0.0)
                other_good = sum(v for k, v in parent_inv.items()
                                 if is_good_currency(k) and k != 'Good Moon' and v > 0.001)
                total_value = good_moon_val + (other_good / 2.0)
                cv = asp_pct * total_value * scaling
                if cv > 0.001:
                    clone_inv['Good Moon'] = cv
                clone_debt = 0.0
                clone_type = 'Passive'

            original_inv = defaultdict(float, clone_inv)
            clones.append({
                'parent': cp, 'offset': offset, 'aspect_pct': asp_pct, 'L': clone_L,
                'inventory': clone_inv, 'original_inventory': original_inv,
                'wasted_inventory': defaultdict(float),
                'debt': clone_debt, 'initial_debt': clone_debt,
                'type': clone_type, 'is_xsun': is_xsun,
            })
        _all_planet_clones[cp] = clones

    # 10.5 Negative-status malefic clone debt scaling (Saturn / Mars / Sun)
    for vsp in ('Saturn', 'Mars', 'Sun'):
        vsp_status_raw = planet_data[vsp].get('updated_status', '-')
        vsp_status = vsp_status_raw if vsp_status_raw not in ('-', '', None) else planet_data[vsp].get('status', '')
        if vsp_status not in _neg_statuses:
            continue
        for vcl in _all_planet_clones.get(vsp, []):
            if vcl['debt'] >= 0:
                continue
            tot = sum(v for v in vcl['inventory'].values() if v > 0.001)
            if tot < 0.001:
                continue
            vcl['debt'] *= (tot / 120.0)

    # 10.6 PASS 2 — sequential exchange + Jupiter Poison
    _jp_poison_case_final = None

    for cp in PLANET_SEQUENCE:
        if cp not in ASPECT_RULES:
            continue
        clones = _all_planet_clones[cp]

        # ── Jupiter Poison ─────────────────────────────────────────────
        if cp == 'Jupiter':
            _jp_sign = planet_sign_map.get('Jupiter', '')
            _jp_L = phase5_data['Jupiter']['L']
            _jp_inv = phase5_data['Jupiter']['p5_inventory']
            _jp_current_val = _jp_inv.get('Jupiter', 0.0)
            jp_mult = 0.0
            jp_case = None

            if _jp_current_val > 0.001:
                def _jp_malefic_free_zone():
                    chk = ['Saturn', 'Mars', 'Rahu']
                    if phase5_data['Ketu']['p5_inventory'].get('Bad Ketu', 0.0) > 0.001:
                        chk.append('Ketu')
                    if _is_moon_malefic_p5():
                        chk.append('Moon')
                    for mp in chk:
                        d = abs(_jp_L - phase5_data[mp]['L'])
                        if d > 180: d = 360 - d
                        if d < 22:
                            return False
                    for cl in _all_leftover_clones:
                        if cl['parent'] in ('Saturn', 'Mars'):
                            d = abs(_jp_L - cl['L'])
                            if d > 180: d = 360 - d
                            if d < 22:
                                tot = sum(v for v in cl['inventory'].values() if v > 0.001)
                                bad = sum(v for k, v in cl['inventory'].items() if v > 0.001 and 'Bad' in k)
                                bad_pct = (bad / tot * 100.0) if tot > 0.001 else 0.0
                                if bad_pct > 5.0:
                                    return False
                    return True

                jp_in_pari = 'Jupiter' in parivardhana_map

                # Case A — Jupiter-Venus
                case_a_mult = 0.0
                if (_jp_sign in {'Sagittarius', 'Pisces', 'Libra', 'Taurus', 'Cancer'}) or jp_in_pari:
                    _venus_L = phase5_data['Venus']['L']
                    jv = abs(_jp_L - _venus_L)
                    if jv > 180: jv = 360 - jv
                    jv_gap = int(jv)
                    if jv_gap <= 28 and _jp_malefic_free_zone():
                        cap_pct = max(50.0, 100.0 - (jv_gap * (50.0 / 22.0))) if jv_gap <= 22 else 50.0
                        case_a_mult = (cap_pct / 100.0) * 0.5

                # Case B — Jupiter-Moon
                case_b_mult = 0.0
                if (_jp_sign in {'Sagittarius', 'Pisces', 'Cancer'}) or jp_in_pari:
                    moon_good_pct = planet_data['Moon'].get('moon_good_pct', 0)
                    moon_bad_pct  = planet_data['Moon'].get('moon_bad_pct', 0)
                    moon_is_waxing = (paksha == 'Shukla') or (moon_phase_name == 'Purnima')
                    moon_phase_ok = (moon_is_waxing and moon_good_pct > 50) or \
                                    (not moon_is_waxing and moon_bad_pct < 10)
                    moon_inv = phase5_data['Moon']['p5_inventory']
                    moon_bad_curr = moon_inv.get('Bad Moon', 0.0)
                    moon_total = sum(abs(v) for v in moon_inv.values())
                    moon_pure = moon_total < 0.001 or (moon_bad_curr / moon_total) < 0.02
                    if moon_phase_ok and moon_pure:
                        _moon_L = phase5_data['Moon']['L']
                        jm = abs(_jp_L - _moon_L)
                        if jm > 180: jm = 360 - jm
                        jm_gap = int(jm)
                        if jm_gap <= 28 and _jp_malefic_free_zone():
                            cap_pct = max(50.0, 100.0 - (jm_gap * (50.0 / 22.0))) if jm_gap <= 22 else 50.0
                            case_b_mult = cap_pct / 100.0

                if case_a_mult > 0.001 or case_b_mult > 0.001:
                    if case_a_mult >= case_b_mult:
                        jp_mult, jp_case = case_a_mult, 'CaseA_Venus'
                    else:
                        jp_mult, jp_case = case_b_mult, 'CaseB_Moon'
                    _jp_poison_case_final = jp_case

                if jp_mult > 0.001:
                    poison = jp_mult * _jp_current_val
                    _jp_inv['Jupiter'] = _jp_current_val - poison
                    _jp_inv['Jupiter Poison'] = _jp_inv.get('Jupiter Poison', 0.0) + poison
                    for jcl in clones:
                        jv = jcl['inventory'].get('Jupiter', 0.0)
                        if jv > 0.001:
                            cp2 = jp_mult * jv
                            jcl['inventory']['Jupiter'] = jv - cp2
                            jcl['inventory']['Jupiter Poison'] = jcl['inventory'].get('Jupiter Poison', 0.0) + cp2
                            jov = jcl['original_inventory'].get('Jupiter', 0.0)
                            if jov > 0.001:
                                op = jp_mult * jov
                                jcl['original_inventory']['Jupiter'] = jov - op
                                jcl['original_inventory']['Jupiter Poison'] = \
                                    jcl['original_inventory'].get('Jupiter Poison', 0.0) + op

        # ── Interaction Cycle (Steps 1-4) ───────────────────────────────
        p5_cycle_limit = 500
        for _cycle in range(p5_cycle_limit):
            something = False
            for clone in clones:
                clone_L = clone['L']

                # Step 1 — Active malefic clones pull from real planets
                if clone['type'] == 'Active' and clone['debt'] < -0.001:
                    cparent = clone['parent']
                    cp_is_mal = cparent in malefic_planets
                    cp_mal_rank = navamsa_malefic_hierarchy.get(cparent, 99)
                    cp_dbt_idx = debtor_rank.index(cparent) if cparent in debtor_rank else 99
                    targets = []
                    for tp in PLANET_ORDER:
                        if tp == cparent: continue
                        if cparent == 'Ketu' and tp not in ('Sun', 'Moon'): continue
                        tp_is_mal = tp in malefic_planets
                        if cp_is_mal and tp_is_mal:
                            if cp_mal_rank >= navamsa_malefic_hierarchy.get(tp, 99):
                                continue
                        else:
                            t_idx = debtor_rank.index(tp) if tp in debtor_rank else 99
                            if cp_dbt_idx > t_idx:
                                continue
                        d = abs(clone_L - phase5_data[tp]['L'])
                        if d > 180: d = 360 - d
                        gap = int(d)
                        if gap <= 22:
                            targets.append({'planet': tp, 'gap': gap})
                    targets.sort(key=lambda x: x['gap'])

                    for t_info in targets:
                        if clone['debt'] >= -0.001:
                            break
                        tp = t_info['planet']
                        gap = t_info['gap']
                        cap_pct = mix_dict.get(gap, 0)
                        max_pull = phase5_data[tp]['volume'] * cap_pct / 100.0
                        tk = f"clone_{clone['parent']}_{clone['offset']}_pulled_from_{tp}"
                        already = clone.get(tk, 0.0)
                        rem = max_pull - already
                        if rem <= 0.001: continue
                        banned = f"Good {cparent}"
                        tinv = phase5_data[tp]['p5_inventory']
                        goods, bads = [], []
                        for k, v in tinv.items():
                            if k == 'Good Rahu' or k == banned: continue
                            if v > 0.001:
                                rec = {'key': k, 'value': v, 'score': _get_p5_currency_rank_score(k)}
                                (goods if is_good_currency(k) else bads).append(rec)
                        goods.sort(key=lambda x: -x['score'])
                        bads.sort(key=lambda x: -x['score'])

                        for curr in goods:
                            if clone['debt'] >= -0.001 or rem <= 0.001: break
                            avail = tinv[curr['key']]
                            if avail <= 0.001: continue
                            take = min(1.0, abs(clone['debt']), avail, rem)
                            if take > 0.001:
                                phase5_data[tp]['p5_inventory'][curr['key']] -= take
                                phase5_data[tp]['p5_current_debt']            -= take
                                clone['inventory'][curr['key']]        = clone['inventory'].get(curr['key'], 0.0) + take
                                clone['wasted_inventory'][curr['key']] = clone['wasted_inventory'].get(curr['key'], 0.0) + take
                                clone['debt'] += take
                                clone[tk] = already + take
                                rem -= take; already += take
                                something = True
                                tp_is_mal_eff = (tp in malefic_planets) or (tp == 'Moon' and phase5_data['Moon'].get('bad_inv', 0) > 0)
                                if cp_is_mal and tp_is_mal_eff:
                                    inf = f"Bad {cparent}"
                                    phase5_data[tp]['p5_inventory'][inf] = phase5_data[tp]['p5_inventory'].get(inf, 0.0) + take

                        good_avail = any(tinv.get(c['key'], 0) > 0.001 for c in goods)
                        if clone['debt'] < -0.001 and not good_avail:
                            for curr in bads:
                                if clone['debt'] >= -0.001 or rem <= 0.001: break
                                avail = tinv[curr['key']]
                                if avail <= 0.001: continue
                                take = min(1.0, abs(clone['debt']), avail, rem)
                                if take > 0.001:
                                    phase5_data[tp]['p5_inventory'][curr['key']] -= take
                                    phase5_data[tp]['p5_current_debt']            -= take
                                    if 'Bad' in curr['key']:
                                        phase5_data[tp]['bad_inv'] -= take
                                    clone['inventory'][curr['key']]        = clone['inventory'].get(curr['key'], 0.0) + take
                                    clone['wasted_inventory'][curr['key']] = clone['wasted_inventory'].get(curr['key'], 0.0) + take
                                    clone['debt'] += take
                                    clone[tk] = already + take
                                    rem -= take; already += take
                                    something = True
                                    tp_is_mal_eff = (tp in malefic_planets) or (tp == 'Moon' and phase5_data['Moon'].get('bad_inv', 0) > 0)
                                    if cp_is_mal and tp_is_mal_eff:
                                        inf = f"Bad {cparent}"
                                        phase5_data[tp]['p5_inventory'][inf] = phase5_data[tp]['p5_inventory'].get(inf, 0.0) + take

                # Step 2 — Real malefics pull from clone's original inventory
                tot_orig_rem = 0.0
                for k in clone['original_inventory']:
                    taken = clone.get(f'taken_from_original_{k}', 0.0)
                    rem_o = clone['original_inventory'][k] - taken
                    if rem_o > 0.001:
                        tot_orig_rem += rem_o
                if tot_orig_rem > 0.001:
                    real_mal = list(P5_MAL_DEBTOR_RANK)
                    if _is_moon_malefic_p5() and 'Moon' not in real_mal:
                        moon_vol = phase5_data['Moon']['volume']
                        if moon_vol > 0:
                            bp = (phase5_data['Moon']['bad_inv'] / moon_vol) * 100
                            mi = real_mal.index('Mars')
                            if bp > 25:
                                real_mal.insert(mi, 'Moon')
                            else:
                                real_mal.insert(mi + 1, 'Moon')
                    for mal in real_mal:
                        if phase5_data[mal]['p5_current_debt'] >= -0.001: continue
                        if mal == 'Ketu' and clone['parent'] not in ('Sun', 'Moon', 'Jupiter', 'Venus', 'Mercury'):
                            continue
                        d = abs(phase5_data[mal]['L'] - clone_L)
                        if d > 180: d = 360 - d
                        gap = int(d)
                        if gap > 22: continue
                        tot_orig_vol = sum(clone['original_inventory'].values())
                        cap_pct = mix_dict.get(gap, 0)
                        max_pull = tot_orig_vol * cap_pct / 100.0
                        tk = f"p5_pulled_from_clone_{clone['parent']}_{clone['offset']}"
                        already = phase5_data[mal].get(tk, 0.0)
                        rem = max_pull - already
                        if rem <= 0.001: continue
                        avail_curr = []
                        for k, ov in clone['original_inventory'].items():
                            if k == 'Good Rahu': continue
                            taken = clone.get(f'taken_from_original_{k}', 0.0)
                            ro = ov - taken
                            if ro > 0.001 and is_good_currency(k):
                                avail_curr.append({'key': k, 'remaining': ro, 'score': _get_p5_currency_rank_score(k)})
                        avail_curr.sort(key=lambda x: -x['score'])
                        for curr in avail_curr:
                            if phase5_data[mal]['p5_current_debt'] >= -0.001 or rem <= 0.001: break
                            tk2 = f"taken_from_original_{curr['key']}"
                            taken = clone.get(tk2, 0.0)
                            ro = clone['original_inventory'][curr['key']] - taken
                            if ro <= 0.001: continue
                            take = min(1.0, abs(phase5_data[mal]['p5_current_debt']), ro, rem)
                            if take > 0.001:
                                clone[tk2] = taken + take
                                clone['inventory'][curr['key']] -= take
                                phase5_data[mal]['p5_inventory'][curr['key']] += take
                                phase5_data[mal]['p5_current_debt']            += take
                                phase5_data[mal][tk] = already + take
                                rem -= take; already += take
                                something = True

                # Step 3 — Real benefics pull from clone's original inventory
                tot_orig_rem = 0.0
                for k in clone['original_inventory']:
                    taken = clone.get(f'taken_from_original_{k}', 0.0)
                    rem_o = clone['original_inventory'][k] - taken
                    if rem_o > 0.001:
                        tot_orig_rem += rem_o
                if tot_orig_rem > 0.001:
                    real_ben = list(P5_BENEFICS)
                    if not _is_moon_malefic_p5():
                        real_ben.append('Moon')
                    def _ben_debt_pct(p):
                        v = phase5_data[p]['volume']
                        return (abs(phase5_data[p]['p5_current_debt']) / v * 100) if v > 0 else 0
                    real_ben.sort(key=lambda p: -_ben_debt_pct(p))
                    for ben in real_ben:
                        if phase5_data[ben]['p5_current_debt'] >= -0.001: continue
                        d = abs(phase5_data[ben]['L'] - clone_L)
                        if d > 180: d = 360 - d
                        gap = int(d)
                        if gap > 22: continue
                        tot_orig_vol = sum(clone['original_inventory'].values())
                        cap_pct = mix_dict.get(gap, 0)
                        max_pull = tot_orig_vol * cap_pct / 100.0
                        tk = f"p5_benefic_pulled_from_clone_{clone['parent']}_{clone['offset']}"
                        already = phase5_data[ben].get(tk, 0.0)
                        rem = max_pull - already
                        if rem <= 0.001: continue
                        avail_curr = []
                        for k, ov in clone['original_inventory'].items():
                            if k == 'Good Rahu': continue
                            taken = clone.get(f'taken_from_original_{k}', 0.0)
                            ro = ov - taken
                            if ro > 0.001 and is_good_currency(k):
                                avail_curr.append({'key': k, 'remaining': ro, 'score': _get_p5_currency_rank_score(k)})
                        avail_curr.sort(key=lambda x: -x['score'])
                        for curr in avail_curr:
                            if phase5_data[ben]['p5_current_debt'] >= -0.001 or rem <= 0.001: break
                            tk2 = f"taken_from_original_{curr['key']}"
                            taken = clone.get(tk2, 0.0)
                            ro = clone['original_inventory'][curr['key']] - taken
                            if ro <= 0.001: continue
                            take = min(1.0, abs(phase5_data[ben]['p5_current_debt']), ro, rem)
                            if take > 0.001:
                                clone[tk2] = taken + take
                                clone['inventory'][curr['key']] -= take
                                phase5_data[ben]['p5_inventory'][curr['key']] += take
                                phase5_data[ben]['p5_current_debt']            += take
                                phase5_data[ben][tk] = already + take
                                rem -= take; already += take
                                something = True

                # Step 4 — Saturn absorbs Bad Sun from XSUN clones
                if clone.get('is_xsun') and clone['inventory'].get('Bad Sun', 0.0) > 0.001:
                    sat_L = phase5_data['Saturn']['L']
                    d = abs(sat_L - clone_L)
                    if d > 180: d = 360 - d
                    gap = int(d)
                    if gap <= 22:
                        tot_vol = sum(v for v in clone['original_inventory'].values() if v > 0.001)
                        cap_pct = mix_dict.get(gap, 0)
                        max_pull = tot_vol * cap_pct / 100.0
                        tk = f"p5_saturn_xsun_{clone['offset']}"
                        already = phase5_data['Saturn'].get(tk, 0.0)
                        rem = max_pull - already
                        if rem > 0.001:
                            avail = clone['inventory'].get('Bad Sun', 0.0)
                            take = min(1.0, avail, rem)
                            if take > 0.001:
                                clone['inventory']['Bad Sun'] -= take
                                phase5_data['Saturn']['p5_inventory']['Bad Sun'] = \
                                    phase5_data['Saturn']['p5_inventory'].get('Bad Sun', 0.0) + take
                                phase5_data['Saturn']['p5_current_debt'] -= take
                                phase5_data['Saturn']['bad_inv'] = phase5_data['Saturn'].get('bad_inv', 0.0) + take
                                phase5_data['Saturn'][tk] = already + take
                                something = True
            if not something:
                break

        # Kill logic — destroy gained currencies in active clones
        for clone in clones:
            if clone['type'] != 'Active':
                continue
            for k in list(clone['inventory'].keys()):
                cur = clone['inventory'].get(k, 0.0)
                if cur <= 0.001:
                    continue
                ov = clone['original_inventory'].get(k, 0.0)
                tk = f'taken_from_original_{k}'
                taken_orig = clone.get(tk, 0.0)
                orig_rem = max(0.0, ov - taken_orig)
                gained = cur - orig_rem
                if gained > 0.001:
                    clone['inventory'][k] = cur - gained
                    if not is_good_currency(k):
                        clone['debt'] -= gained

        for clone in clones:
            _all_leftover_clones.append(clone)

    # 10.7 Sun Healing Pull (real Sun from real Mars/Mercury, with 0.5 healing)
    _sun_L = phase5_data['Sun']['L']
    _sun_heal_targets = []
    for shp in ('Mars', 'Mercury'):
        d = abs(_sun_L - phase5_data[shp]['L'])
        if d > 180: d = 360 - d
        gap = int(d)
        if gap <= 22:
            _sun_heal_targets.append((shp, gap))
    _sun_heal_targets.sort(key=lambda x: x[1])
    if _sun_heal_targets and phase5_data['Sun']['p5_current_debt'] < -0.001:
        for _ in range(500):
            did = False
            for shp, gap in _sun_heal_targets:
                if phase5_data['Sun']['p5_current_debt'] >= -0.001:
                    break
                cap_pct = mix_dict.get(gap, 0)
                max_pull = phase5_data[shp]['volume'] * cap_pct / 100.0
                tk = f"sun_heal_pulled_from_{shp}"
                already = phase5_data['Sun'].get(tk, 0.0)
                rem = max_pull - already
                if rem <= 0.001: continue
                inv = phase5_data[shp]['p5_inventory']
                avail = []
                for k, v in inv.items():
                    if k == 'Good Rahu': continue
                    if v > 0.001 and is_good_currency(k):
                        avail.append((k, v, _get_p5_currency_rank_score(k)))
                avail.sort(key=lambda x: -x[2])
                for k, _v, _s in avail:
                    if phase5_data['Sun']['p5_current_debt'] >= -0.001 or rem <= 0.001:
                        break
                    cur = inv.get(k, 0.0)
                    if cur <= 0.001: continue
                    take = min(1.0, abs(phase5_data['Sun']['p5_current_debt']), cur, rem)
                    if take > 0.001:
                        phase5_data[shp]['p5_inventory'][k] -= take
                        phase5_data[shp]['p5_current_debt']  -= take
                        phase5_data['Sun']['p5_inventory'][k] = phase5_data['Sun']['p5_inventory'].get(k, 0.0) + take
                        phase5_data['Sun']['p5_current_debt'] += take
                        heal_key = f"Good {shp}"
                        heal = take * 0.5
                        phase5_data[shp]['p5_inventory'][heal_key] = phase5_data[shp]['p5_inventory'].get(heal_key, 0.0) + heal
                        phase5_data[shp]['p5_current_debt'] += heal
                        phase5_data['Sun'][tk] = already + take
                        rem -= take; already += take
                        did = True
            if not did:
                break

    # 10.8 Jupiter Poison post-sharing debt application
    _jp_debt_mult = 1.0 if _jp_poison_case_final == 'CaseB_Moon' else \
                   (0.5 if _jp_poison_case_final == 'CaseA_Venus' else 0.0)
    for jpp in PLANET_ORDER:
        held = phase5_data[jpp]['p5_inventory'].get('Jupiter Poison', 0.0)
        if held > 0.001:
            phase5_data[jpp]['p5_current_debt'] -= _jp_debt_mult * held
    for jcl in _all_leftover_clones:
        held = jcl['inventory'].get('Jupiter Poison', 0.0)
        if held > 0.001:
            jcl['debt'] -= _jp_debt_mult * held

    # 10.9 Ketu alone & unaspected (sign-based, no lagna)
    _ketu_lonely = {'Gemini', 'Leo', 'Scorpio', 'Aquarius'}
    if planet_sign_map.get('Ketu') in _ketu_lonely:
        ketu_L = phase5_data['Ketu']['L']
        alone = True
        for cp_chk in ('Sun', 'Moon', 'Mars', 'Mercury', 'Jupiter', 'Venus', 'Saturn', 'Rahu'):
            d = abs(ketu_L - phase5_data[cp_chk]['L'])
            if d > 180: d = 360 - d
            if d < 22:
                alone = False
                break
        if alone:
            for cl in _all_leftover_clones:
                d = abs(ketu_L - cl['L'])
                if d > 180: d = 360 - d
                if d < 22:
                    alone = False
                    break
        if alone:
            phase5_data['Ketu']['p5_inventory']['Bad Ketu'] = \
                phase5_data['Ketu']['p5_inventory'].get('Bad Ketu', 0.0) + 25.0
            phase5_data['Ketu']['p5_current_debt'] -= 25.0

    # 10.10 Jupiter Poison penalty multipliers (used in net-score & KHS scoring)
    if _jp_poison_case_final == 'CaseB_Moon':
        poisonpenality = 2
        poisonpenality_1 = 1
    elif _jp_poison_case_final == 'CaseA_Venus':
        poisonpenality = 1
        poisonpenality_1 = 0.5
    else:
        poisonpenality = 0
        poisonpenality_1 = 0

    # 10.11 KHS — sign-based aspect_score + occupant_score (no lagna logic)
    aspect_score = {s: 0.0 for s in sign_names}
    occupant_score = {s: 0.0 for s in sign_names}

    def _hp_is_malefic(name):
        if name in ('Saturn', 'Mars', 'Sun', 'Rahu'):
            return True
        if name == 'Moon':
            return phase5_data['Moon']['bad_inv'] > 0.001
        if name == 'Ketu':
            return phase5_data['Ketu']['p5_inventory'].get('Bad Ketu', 0.0) > 0.001
        return False

    _own_good_key = {
        'Saturn': 'Good Saturn', 'Mars': 'Good Mars', 'Sun': 'Good Sun',
        'Rahu': 'Good Rahu', 'Ketu': 'Good Ketu', 'Moon': 'Good Moon',
    }

    # Aspect contribution from clones
    for clone in _all_leftover_clones:
        if clone.get('is_xsun'):
            continue
        parent = clone['parent']
        # Rahu and Ketu do not cast aspects in KHS
        if parent in ('Rahu', 'Ketu'):
            continue
        target_lon = (phase5_data[parent]['L'] + (clone['offset'] - 1) * 30) % 360
        target_sign = get_sign(target_lon)
        if _hp_is_malefic(parent):
            if parent == 'Mars' and target_sign == 'Leo':
                other_bad = sum(v for k, v in clone['inventory'].items()
                                if 'Bad' in k and k != 'Bad Mars' and v > 0.001)
                if other_bad > 0.001:
                    aspect_score[target_sign] -= other_bad
            elif clone['debt'] < -0.001:
                penalty = abs(clone['debt'])
                aspect_score[target_sign] -= penalty
            own_key = _own_good_key.get(parent)
            if own_key:
                ov = clone['inventory'].get(own_key, 0.0)
                if ov > 0.001:
                    aspect_score[target_sign] += ov
        else:
            good_total = sum(v for k, v in clone['inventory'].items()
                             if v > 0.001 and is_good_currency(k))
            poison_held = clone['inventory'].get('Jupiter Poison', 0.0)
            if poison_held > 0.001:
                good_total -= poison_held
            if good_total > 0.001:
                aspect_score[target_sign] += good_total
            if poison_held > 0.001:
                aspect_score[target_sign] -= (poisonpenality - 1) * poison_held

    # Occupant contribution
    sign_occupants = defaultdict(list)
    for pn in PLANET_ORDER:
        sign_occupants[planet_sign_map[pn]].append(pn)
    for s in sign_names:
        for occ in sign_occupants.get(s, []):
            inv = phase5_data[occ]['p5_inventory']
            if _hp_is_malefic(occ):
                tg = sum(v for k, v in inv.items() if v > 0.001 and is_good_currency(k))
                tb = sum(v for k, v in inv.items() if v > 0.001 and 'Bad' in k)
                ph = inv.get('Jupiter Poison', 0.0)
                if ph > 0.001:
                    tg -= ph
                    tb += (poisonpenality - 1) * ph
                occupant_score[s] += (tg - tb)
            else:
                tg = sum(v for k, v in inv.items() if v > 0.001 and is_good_currency(k))
                ph = inv.get('Jupiter Poison', 0.0)
                if ph > 0.001:
                    tg -= ph
                if tg > 0.001:
                    occupant_score[s] += tg
                if ph > 0.001:
                    occupant_score[s] -= (poisonpenality - 1) * ph

    # Subtract used gift-pot amount per sign from occupant_score
    for gs, cfg in gift_cfg.items():
        original_pot = phase4_pot_initial.get(gs, 0.0)
        leftover     = phase4_pot_remaining.get(gs, 0.0)
        used = original_pot - leftover
        if used > 0.001:
            occupant_score[gs] -= used

    # 10.12 Alias for Final NPS step
    p5_data = phase5_data

    # ── 11. Final NPS computation ─────────────────────────────────────
    out_planets = {}
    for p in PLANET_ORDER:
        d = p5_data[p]
        cap = capacity_dict.get(p, None)
        vol = d['volume']
        debt = d['p5_current_debt']
        inv = d['p5_inventory']
        # Sums (Jupiter Poison treated as bad with poisonpenality_1 weight)
        total_good = 0.0
        total_bad  = 0.0
        for k, v in inv.items():
            if v <= 0:
                continue
            if k == 'Jupiter Poison':
                total_bad += poisonpenality_1 * v
            elif is_good_currency(k):
                total_good += v
            else:
                total_bad += v
        net_score = total_good - total_bad
        status = planet_data[p]['status']
        is_neecham = (status == 'Neecham' and
                      planet_data[p]['updated_status'] != 'Neechabhangam')
        is_benefic = p in ('Jupiter', 'Venus', 'Mercury') or (
            p == 'Moon' and moon_is_benefic_p2)

        # Case formulas (verbatim from logic.py)
        if p == 'Moon' and moon_is_benefic_p2 and not is_neecham:
            final_ns = ((vol + debt) / vol) * 100 if vol > 0 else 0
            case = 'A'
        elif p == 'Moon' and moon_is_benefic_p2 and is_neecham:
            final_ns = ((total_good - (-debt)) / (cap * 1.2)) * 120 if cap else 0
            case = 'B'
        elif is_benefic and is_neecham:
            final_ns = (net_score / (cap * 1.2)) * 120 if cap else 0
            case = 'C'
        elif is_neecham:
            final_ns = ((cap * 1.2 + debt) / (cap * 1.2)) * 120 if cap else 0
            case = 'D'
        elif is_benefic:
            final_ns = ((vol + debt) / vol) * 100 if vol > 0 else 0
            case = 'E'
        else:
            final_ns = ((vol + debt) / vol) * 100 if vol > 0 else 0
            case = 'F'

        # KHS contribution (capped at +20, no lower cap)
        ruled = planet_ruled_signs.get(p, [])
        if ruled:
            khs_total = sum(aspect_score.get(rs, 0.0) + occupant_score.get(rs, 0.0) for rs in ruled)
            khs_avg = khs_total / len(ruled)
            khs_val = min((khs_avg / 10.0) * 2.0, 20.0)
        else:
            khs_val = 0.0
        ns_without_khs = final_ns
        final_ns += khs_val

        # Predictions normalisation
        if is_benefic:
            pred_norm = max(0.0, min(100.0, (final_ns ** 2) / 100.0))
        else:
            pred_norm = min(100.0, (100 + final_ns) / 2)

        out_planets[p] = {
            'sign': planet_data[p]['sign'],
            'longitude': round(planet_data[p]['L'], 4),
            'status': status,
            'updated_status': planet_data[p]['updated_status'],
            'sthana': planet_data[p]['sthana'],
            'volume': round(vol, 2),
            'debt': round(debt, 2),
            'good_total': round(total_good, 2),
            'bad_total': round(total_bad, 2),
            'net_score': round(net_score, 2),
            'khs': round(khs_val, 2),
            'nps_without_khs': round(ns_without_khs, 2),
            'final_nps': round(final_ns, 2),
            'pred_norm': round(pred_norm, 2),
            'formula_case': case,
            'inventory': {k: round(v, 2) for k, v in inv.items() if abs(v) > 0.001},
        }

    return {
        'as_of_utc': utc_dt.isoformat(),
        'as_of_local': local_dt.isoformat(),
        'tz': tz_name,
        'jd': jd,
        'paksha': paksha,
        'tithi_name': moon_phase_name,
        'jupiter_poison_case': _jp_poison_case_final,
        'parivardhana_map': parivardhana_map,
        'planets': out_planets,
        'phases': {
            'phase0': {p: {'inventory': {k: round(v, 2) for k, v in s['inventory'].items() if abs(v) > 0.001},
                           'debt': round(s['debt'], 2)} for p, s in _snap_phase0.items()},
            'phase2': {p: {'inventory': {k: round(v, 2) for k, v in s['inventory'].items() if abs(v) > 0.001},
                           'debt': round(s['debt'], 2)} for p, s in _snap_phase2.items()},
            'phase2b': {p: {'inventory': {k: round(v, 2) for k, v in s['inventory'].items() if abs(v) > 0.001},
                            'debt': round(s['debt'], 2)} for p, s in _snap_phase2b.items()},
            'phase4': {p: {'inventory': {k: round(v, 2) for k, v in s['inventory'].items() if abs(v) > 0.001},
                           'debt': round(s['debt'], 2)} for p, s in _snap_phase4.items()},
            'phase5': {p: {'inventory': out_planets[p]['inventory'],
                           'debt': out_planets[p]['debt']} for p in PLANET_ORDER},
        },
        'khs_breakdown': {
            'aspect_score': {s: round(v, 2) for s, v in aspect_score.items()},
            'occupant_score': {s: round(v, 2) for s, v in occupant_score.items()},
        },
        'clones': [
            {
                'parent': cl['parent'], 'offset': cl['offset'],
                'L': round(cl['L'], 2), 'type': cl['type'],
                'is_xsun': cl.get('is_xsun', False),
                'initial_debt': round(cl['initial_debt'], 2),
                'final_debt': round(cl['debt'], 2),
                'inventory': {k: round(v, 2) for k, v in cl['inventory'].items() if abs(v) > 0.001},
            }
            for cl in _all_leftover_clones
        ],
    }


# ──────────────────────────────────────────────────────────────────────
# Streamlit UI
# ──────────────────────────────────────────────────────────────────────

# Vedic graha drishti: from-house → list of houses aspected.
# All planets aspect 7th. Mars +4,8. Jupiter +5,9. Saturn +3,10.
# Rahu/Ketu +5,9 (common usage).
_ASPECT_HOUSES = {
    'Sun':     [7],
    'Moon':    [7],
    'Mercury': [7],
    'Venus':   [7],
    'Mars':    [4, 7, 8],
    'Jupiter': [5, 7, 9],
    'Saturn':  [3, 7, 10],
    'Rahu':    [5, 7, 9],
    'Ketu':    [5, 7, 9],
}


_TRANSITDATA_CACHE: "dict | None" = None


def _load_transitdata() -> dict:
    """Load transitdata.json once per process and cache in a module-level dict."""
    global _TRANSITDATA_CACHE
    if _TRANSITDATA_CACHE is None:
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'transitdata.json')
        try:
            with open(path, 'r', encoding='utf-8') as f:
                _TRANSITDATA_CACHE = json.load(f)
        except Exception:
            _TRANSITDATA_CACHE = {}
    return _TRANSITDATA_CACHE


def _build_house_table(result: dict, lagna_sign: str) -> pd.DataFrame:
    """Build the 12-house table given a chosen Lagna sign."""
    lagna_idx = sign_names.index(lagna_sign)
    # House n (1..12) sign
    house_sign  = {n: sign_names[(lagna_idx + n - 1) % 12] for n in range(1, 13)}
    sign_house  = {s: n for n, s in house_sign.items()}

    # Planets per house
    planets_in_house = {n: [] for n in range(1, 13)}
    for p in PLANET_ORDER:
        s = result['planets'][p]['sign']
        planets_in_house[sign_house[s]].append(p)

    # Aspects: for each occupant planet, fill the houses it aspects
    aspects_in_house = {n: [] for n in range(1, 13)}
    for p in PLANET_ORDER:
        s = result['planets'][p]['sign']
        from_house = sign_house[s]
        for off in _ASPECT_HOUSES.get(p, [7]):
            target = ((from_house - 1 + off - 1) % 12) + 1
            aspects_in_house[target].append(p)

    rows = []
    for n in range(1, 13):
        sg = house_sign[n]
        lord = get_sign_lord(sg)
        lord_sign = result['planets'].get(lord, {}).get('sign')
        lord_house = sign_house.get(lord_sign, '-')
        occupants = planets_in_house[n]
        if n == 1:
            occ_str = 'Asc' + (' + ' + ', '.join(occupants) if occupants else '')
        else:
            occ_str = ', '.join(occupants) if occupants else 'Empty'
        asps = aspects_in_house[n]
        asp_str = ', '.join(asps) if asps else 'None'
        rows.append({
            'House':       f'House {n}',
            'Sign':        sg,
            'Planets':     occ_str,
            'Aspects from': asp_str,
            'Lord':        lord,
            'Lord in':     f'House {lord_house}' if isinstance(lord_house, int) else '-',
        })
    return pd.DataFrame(rows)


def _phase_delta_table(result: dict, planet: str) -> pd.DataFrame:
    """Inventory across all phases for a single planet, plus debt row."""
    phases = ['phase0', 'phase2', 'phase2b', 'phase4', 'phase5']
    labels = ['Phase 0\n(initial)', 'Phase 2\n(malefic pull)',
              'Phase 2b\n(benefic redist.)', 'Phase 4\n(gift pots)',
              'Phase 5\n(clones + KHS)']
    # Collect every currency that ever appears
    all_keys = set()
    for ph in phases:
        all_keys.update(result['phases'][ph][planet]['inventory'].keys())
    rows = []
    for k in sorted(all_keys):
        row = {'Currency': k}
        for ph, lbl in zip(phases, labels):
            row[lbl] = result['phases'][ph][planet]['inventory'].get(k, 0.0)
        rows.append(row)
    debt_row = {'Currency': '— Debt —'}
    for ph, lbl in zip(phases, labels):
        debt_row[lbl] = result['phases'][ph][planet]['debt']
    rows.append(debt_row)
    return pd.DataFrame(rows)


def _run_streamlit_app():
    import streamlit as st
    st.set_page_config(page_title="Daily Transit NPS", layout="wide")
    st.title("Daily Transit NPS")
    st.caption(
        "Per-planet Net Planetary Strength for any chosen moment. "
        "Computation is house-independent; the house table below is a "
        "display-only overlay driven by the Lagna selector."
    )

    col1, col2, col3 = st.columns([1, 1, 1])
    with col1:
        date_val = st.date_input("Date", value=datetime.now().date(),
                                 min_value=datetime(1, 1, 1).date(),
                                 max_value=datetime(2200, 12, 31).date(),
                                 format="DD/MM/YYYY")
    with col2:
        time_val = st.time_input("Time", value=datetime.now().replace(hour=12, minute=0).time())
    with col3:
        common_tz = ['Asia/Kolkata', 'UTC', 'America/New_York', 'America/Los_Angeles',
                     'Europe/London', 'Asia/Singapore', 'Asia/Tokyo', 'Australia/Sydney']
        tz_val = st.selectbox("Timezone", common_tz, index=0)

    compute_clicked = st.button("Compute Daily NPS", type="primary")

    # Persist the last result in session state so the Lagna dropdown can
    # re-render the house table without recomputing.
    if compute_clicked:
        with st.spinner("Computing planetary state..."):
            try:
                st.session_state['daily_nps_result'] = compute_daily_nps(
                    date_val.strftime("%Y-%m-%d"),
                    time_val.strftime("%H:%M"),
                    tz_val,
                )
            except Exception as exc:
                st.error(f"Computation failed: {exc}")
                return

    result = st.session_state.get('daily_nps_result')
    if not result:
        st.info("Pick date / time / timezone and press **Compute Daily NPS**.")
        return

    st.success(f"Tithi: {result['tithi_name']} ({result['paksha']} Paksha)")
    st.caption(
        f"Local: {result['as_of_local']}  |  UTC: {result['as_of_utc']}  |  "
        f"JD: {result['jd']:.4f}"
    )
    if result.get('jupiter_poison_case'):
        st.warning(f"Jupiter Poison active: {result['jupiter_poison_case']}")

    # ── 1. Headline NPS / Predictions / Strength ────────────────────
    st.subheader("NPS · Predictions · Strength")
    rows = []
    _parivardhana = result.get('parivardhana_map', {})
    for p in PLANET_ORDER:
        d = result['planets'][p]
        p_exchange = "-"
        if p in _parivardhana:
            partner = _parivardhana[p]
            partner_sign = result['planets'][partner]['sign']
            p_exchange = f"Yes, with {partner} [{partner_sign}]"
        
        rows.append({
            'Planet':         p,
            'Sign':           d['sign'],
            'Parivartana':    p_exchange,
            'Long°':          d['longitude'],
            'Status':         d['status'] if d['updated_status'] == '-' else
                              f"{d['status']} → {d['updated_status']}",
            'Strength (Sthana%)': d['sthana'],
            'Volume':         d['volume'],
            'Net':            d['net_score'],
            'Debt':           d['debt'],
            'KHS':            d['khs'],
            'NPS':            d['final_nps'],
            'Predictions %':  d['pred_norm'],
        })
    st.dataframe(pd.DataFrame(rows), use_container_width=True, hide_index=True)

    # ── 1.5 Simplified Final Table ───────────────────────────────────
    st.subheader("Final Strength & Wellness")
    final_rows = []
    for p in PLANET_ORDER:
        d = result['planets'][p]
        capped_nps = min(100.0, d['final_nps'])
        final_rows.append({
            'Planet': p,
            'Total Strength': capped_nps,
            'Wellness Score': d['pred_norm'],
        })
    st.dataframe(pd.DataFrame(final_rows), use_container_width=True, hide_index=True)

    # ── 2. House table (Lagna-driven) ───────────────────────────────
    st.subheader("House Table")
    default_lagna = result['planets']['Sun']['sign']
    try:
        default_idx = sign_names.index(default_lagna)
    except ValueError:
        default_idx = 0
    lagna_sign = st.selectbox(
        "First House (Lagna sign)",
        sign_names,
        index=default_idx,
        help="Pick which sign should be treated as House 1. The table below "
             "(Planets / Aspects / Lord / Lord-in) updates instantly."
    )
    st.dataframe(_build_house_table(result, lagna_sign),
                 use_container_width=True, hide_index=True)

    # ── Export Chart Data ────────────────────────────────────────────
    st.subheader("Export Chart Data")
    st.caption(
        "Downloads a text snapshot for the selected first-house (Lagna) sign, "
        "containing planetary positions, house details, and transit data "
        "(predictions excluded)."
    )

    transit_db     = _load_transitdata()
    lagna_key      = f"{lagna_sign} Lagna"
    lagna_transits = transit_db.get(lagna_key, {})

    lagna_idx     = sign_names.index(lagna_sign)
    house_sign    = {n: sign_names[(lagna_idx + n - 1) % 12] for n in range(1, 13)}
    sign_house    = {s: n for n, s in house_sign.items()}

    # Aspect-percentage rules (mirrors logic.py _PROMPT_ASPECT_RULES)
    _ASPECT_PCT_RULES = {
        'Saturn': {3: 25, 7: 100, 10: 75},
        'Mars':   {4: 40, 7: 100, 8: 25},
        'Sun':    {7: 50},
        'Jupiter':{5: 100, 7: 100, 9: 100},
        'Venus':  {7: 100},
        'Mercury':{7: 100},
        'Moon':   {4: 25, 6: 50, 7: 100, 8: 50, 10: 25},
        'Rahu':   {5: 100, 7: 100, 9: 100},
        'Ketu':   {5: 100, 7: 100, 9: 100},
    }

    _parivardhana_simple = result.get('parivardhana_map', {}) or {}

    # ── 1. Planetary positions ───────────────────────────────
    pp_lines = ["=== PLANETARY POSITIONS ==="]
    asc_deg = lagna_idx * 30.0
    pp_lines.append(f"Asc: Deg: {asc_deg:.2f} | Sign: {lagna_sign}")
    for p in PLANET_ORDER:
        d = result['planets'][p]
        parts = [
            f"Deg: {d.get('longitude', 0):.2f}",
            f"Sign: {d.get('sign', '')}",
        ]
        upd_status = d.get('updated_status', '-')
        status     = d.get('status', '-')
        if upd_status and str(upd_status) not in ('-', 'nan', '', 'None'):
            parts.append(f"Status: {upd_status}")
        elif status and str(status) not in ('-', 'nan', '', 'None'):
            parts.append(f"Status: {status}")
        # Parivardhana: build "Partner (Hx-Hy)" from the simple partner-name map
        if p in _parivardhana_simple:
            partner = _parivardhana_simple[p]
            h_self = sign_house.get(d.get('sign', ''), '?')
            partner_sign = result['planets'].get(partner, {}).get('sign', '')
            h_partner = sign_house.get(partner_sign, '?')
            parts.append(f"Parivardhana: {partner} (H{h_self}-H{h_partner})")
        # NPS / Strength — always for the seven, only NPS for shadow planets
        pred_val = d.get('pred_norm')
        if pred_val is not None:
            parts.append(f"NPS (Predictions): {pred_val:.2f}")
        if p not in ('Rahu', 'Ketu'):
            strength = min(100.0, d.get('final_nps', 0.0))
            parts.append(f"Strength: {strength:.2f}")
        pp_lines.append(f"{p}: {' | '.join(parts)}")

    # ── 2. House details ─────────────────────────────────────
    planets_in_house = {n: [] for n in range(1, 13)}
    for p in PLANET_ORDER:
        s = result['planets'][p].get('sign', '')
        if s in sign_house:
            planets_in_house[sign_house[s]].append(p)

    aspects_in_house = {n: [] for n in range(1, 13)}
    for p in PLANET_ORDER:
        s = result['planets'][p].get('sign', '')
        if s not in sign_house:
            continue
        from_house = sign_house[s]
        for off in _ASPECT_HOUSES.get(p, [7]):
            target = ((from_house - 1 + off - 1) % 12) + 1
            aspects_in_house[target].append(p)

    hd_lines = ["=== HOUSE DETAILS ==="]
    for n in range(1, 13):
        sg = house_sign[n]
        occupants = planets_in_house[n]
        if n == 1:
            contains_str = "Contains Asc" + ((" + " + ", ".join(occupants)) if occupants else "")
        else:
            contains_str = ("Contains " + ", ".join(occupants)) if occupants else "Empty"

        asps = aspects_in_house[n]
        if asps:
            asp_with_pct = []
            for ap in asps:
                ap_sign  = result['planets'][ap].get('sign', '')
                ap_house = sign_house.get(ap_sign, 0)
                if ap_house:
                    offset = ((n - ap_house) % 12) + 1
                    pct = _ASPECT_PCT_RULES.get(ap, {}).get(offset)
                    asp_with_pct.append(f"{ap}({pct}%)" if pct is not None else ap)
                else:
                    asp_with_pct.append(ap)
            aspects_str = ("Aspects from " if len(asp_with_pct) > 1 else "Aspect from ") + ", ".join(asp_with_pct)
        else:
            aspects_str = "No Aspects"

        lord = get_sign_lord(sg)
        lord_sign  = result['planets'].get(lord, {}).get('sign', '')
        lord_house = sign_house.get(lord_sign, '-')
        lord_str   = (f"Lord: {lord} (placed in House {lord_house})"
                      if isinstance(lord_house, int)
                      else f"Lord: {lord}")

        hd_lines.append(f"House {n} ({sg}): {contains_str} | {aspects_str} | {lord_str}")

    # ── 3. Transit data (predictions excluded) ───────────────
    td_lines = ["=== TRANSIT DATA ==="]
    for p in PLANET_ORDER:
        d        = result['planets'][p]
        p_sign   = d.get('sign', '')
        entry    = lagna_transits.get(p, {}).get(p_sign, {})
        if not entry:
            td_lines.append(f"{p} ({p_sign}): (no transit entry)")
            continue
        t_parts = [
            f"rasi: {entry.get('rasi', '')}",
            f"placement_sign: {entry.get('placement_sign', p_sign)}",
            f"lord_of_houses: {entry.get('lord_of_houses', [])}",
            f"in_house: {entry.get('in_house', '')}",
            f"status: {entry.get('status', '')}",
            f"verdict: {entry.get('verdict', '')}",
        ]
        td_lines.append(f"{p} ({p_sign}): " + " | ".join(t_parts))

    export_text = (
        "\n".join(pp_lines)
        + "\n\n"
        + "\n\n".join(hd_lines)
        + "\n\n"
        + "\n".join(td_lines)
        + "\n"
    )

    date_slug = (result.get('as_of_utc') or '')[:10]
    st.download_button(
        label     = "⬇ Download Chart Data (.txt)",
        data      = export_text,
        file_name = f"chart_{lagna_sign}_{date_slug}.txt",
        mime      = "text/plain",
    )
    with st.expander("Preview Export Data"):
        st.text(export_text)

    # ── 3. Phase-by-phase currency exchange ─────────────────────────
    st.subheader("Currency Exchange across Phases")
    st.caption("Phase 0 = initial inventory + Rahu Phase-0 bonus  ·  "
               "Phase 2 = malefic pull (degree-gap)  ·  "
               "Phase 2b = benefic redistribution  ·  "
               "Phase 4 = gift pots (Sag/Pis/Lib/Tau)  ·  "
               "Phase 5 = virtual aspect clones + Jupiter Poison + KHS.")
    planet_pick = st.selectbox("Planet", PLANET_ORDER, index=0,
                               key="phase_planet_pick")
    df_phases = _phase_delta_table(result, planet_pick)
    st.dataframe(df_phases, use_container_width=True, hide_index=True)

    # All-planets compact debt evolution
    with st.expander("Debt evolution — all planets across phases"):
        ph_keys = ['phase0', 'phase2', 'phase2b', 'phase4', 'phase5']
        ph_labels = ['Phase 0', 'Phase 2', 'Phase 2b', 'Phase 4', 'Phase 5']
        debt_rows = []
        for p in PLANET_ORDER:
            row = {'Planet': p}
            for k, lbl in zip(ph_keys, ph_labels):
                row[lbl] = result['phases'][k][p]['debt']
            debt_rows.append(row)
        st.dataframe(pd.DataFrame(debt_rows),
                     use_container_width=True, hide_index=True)

    # ── 4. KHS sign-by-sign breakdown ───────────────────────────────
    with st.expander("KHS — sign-by-sign aspect & occupant scores"):
        khs_rows = []
        for s in sign_names:
            asp = result['khs_breakdown']['aspect_score'].get(s, 0.0)
            occ = result['khs_breakdown']['occupant_score'].get(s, 0.0)
            khs_rows.append({'Sign': s, 'Aspect': asp,
                             'Occupant': occ, 'Total': round(asp + occ, 2)})
        st.dataframe(pd.DataFrame(khs_rows),
                     use_container_width=True, hide_index=True)

    # ── 5. Per-planet inventory expanders (Phase 5 final) ───────────
    with st.expander("Per-planet final (Phase 5) inventories"):
        cols = st.columns(3)
        for i, p in enumerate(PLANET_ORDER):
            d = result['planets'][p]
            with cols[i % 3]:
                st.markdown(f"**{p} — {d['sign']}** · NPS {d['final_nps']:.1f}")
                st.caption(f"Sthana {d['sthana']}% · Volume {d['volume']} · "
                           f"Debt {d['debt']} · KHS {d['khs']}")
                if d['inventory']:
                    inv_rows = [{'Currency': k, 'Amount': v}
                                for k, v in sorted(d['inventory'].items(),
                                                   key=lambda kv: -kv[1])]
                    st.dataframe(pd.DataFrame(inv_rows),
                                 use_container_width=True, hide_index=True)
                else:
                    st.write("_empty_")

    # ── 6. Virtual aspect clones ───────────────────────────────────
    if result.get('clones'):
        with st.expander(f"Virtual aspect clones ({len(result['clones'])})"):
            clone_rows = []
            for cl in result['clones']:
                inv_str = ', '.join(f"{k}[{v:.2f}]" for k, v in cl['inventory'].items()) or '-'
                clone_rows.append({
                    'Parent':       cl['parent'] + (' (XSUN)' if cl['is_xsun'] else ''),
                    'Offset':       cl['offset'],
                    'L (deg)':      cl['L'],
                    'Type':         cl['type'],
                    'Initial Debt': cl['initial_debt'],
                    'Final Debt':   cl['final_debt'],
                    'Inventory':    inv_str,
                })
            st.dataframe(pd.DataFrame(clone_rows),
                         use_container_width=True, hide_index=True)


if __name__ == "__main__":
    # Streamlit only invokes top-level code — guard with a flag check so
    # `python daily_nps.py` doesn't crash trying to render UI to a TTY.
    try:
        import streamlit.runtime.scriptrunner as _ssr  # noqa: F401
        _run_streamlit_app()
    except Exception:
        # Fallback CLI: print today-noon-IST result
        import json as _json
        today = datetime.now().strftime("%Y-%m-%d")
        print(_json.dumps(compute_daily_nps(today, "12:00", "Asia/Kolkata"),
                          indent=2, default=str))
