#!/bin/bash
# NAUbackup-Lauf mit rotierenden LUKS-Wechselplatten (Vorlage, im Einsatz auf busse-xcp01).
# Oeffnet die erste angeschlossene Rotationsplatte, mountet sie, startet VmBackup.py, haengt aus.
# Kann die Platte nicht bereitgestellt werden, meldet VmBackup.py den Abbruch per Mail und API
# (abort=<grund>), statt still zu enden.
# Zugangsdaten liegen in $NB/.secrets (chmod 600): lukspass=, mailuser=, mailpass=, api_token=

NB=/root/naubackup
CFG=$NB/VmBackup.cfg
MNT=/naubackup.store
MAPPER=backup

# Rotationsplatten: die erste gefundene by-id-Kennung wird verwendet.
disks=(usb-WD_My_Passport_2626_575837324442345033415639-0:0
       usb-WD_My_Passport_2626_575841324439354B4C55334A-0:0-part1
       usb-WD_My_Passport_2626_575841324439354B4C383934-0:0-part1)

cryptsetup=/usr/sbin/cryptsetup

abort() {
    echo "ABBRUCH: $1"
    "$NB/VmBackup.py" local "$CFG" "abort=$1"
    exit 2
}

rm -f "$NB/target_state"

if [ ! -r "$NB/.secrets" ]; then
    abort "Datei $NB/.secrets fehlt oder ist nicht lesbar"
fi
. "$NB/.secrets"
if [ -z "$lukspass" ]; then
    abort "lukspass fehlt in $NB/.secrets"
fi

if awk -v m="$MNT" '$2==m{found=1} END{exit !found}' /etc/mtab; then
    abort "Mountpoint $MNT ist noch belegt, vermutlich haengt ein vorheriger Lauf (umount $MNT pruefen)"
fi
if [ -e "/dev/mapper/$MAPPER" ]; then
    echo "LUKS-Mapping $MAPPER ist noch offen, schliesse es."
    $cryptsetup luksClose "$MAPPER" || abort "LUKS-Mapping $MAPPER ist noch offen und laesst sich nicht schliessen"
fi

target=""
for id in "${disks[@]}"; do
    if [ -L "/dev/disk/by-id/$id" ]; then
        echo "Sicherungsziel $id gefunden."
        target="/dev/disk/by-id/$id"
        target_id="$id"
        break
    fi
done
if [ -z "$target" ]; then
    abort "Keine Sicherungsplatte angeschlossen (erwartet eine von ${#disks[@]} Rotationsplatten)"
fi

if ! echo -n "$lukspass" | $cryptsetup luksOpen "$target" "$MAPPER" -d -; then
    abort "Platte $target_id laesst sich nicht entschluesseln (LUKS-Passphrase oder Platte defekt)"
fi
if ! mount "/dev/mapper/$MAPPER" "$MNT"; then
    $cryptsetup luksClose "$MAPPER"
    abort "Platte $target_id laesst sich nicht einhaengen (Dateisystem pruefen: fsck)"
fi

# Plattenkennung fuer den Report: by-id-Name und die Seriennummer vom Aufkleber (Hex im by-id-Namen)
hex=${target_id##*_}; hex=${hex%%-*}
serial=$(python3 -c 'import sys; print(bytes.fromhex(sys.argv[1]).decode("ascii", "replace"))' "$hex" 2>/dev/null)
printf 'target_id=%s\ntarget_serial=%s\n' "$target_id" "$serial" > "$NB/target_state"

"$NB/VmBackup.py" local "$CFG"
rc=$?

sync
if ! umount "$MNT"; then
    echo "WARNUNG: umount $MNT fehlgeschlagen, LUKS-Mapping bleibt offen. Naechster Lauf meldet den belegten Mountpoint."
    exit 1
fi
$cryptsetup luksClose "$MAPPER"
exit $rc
