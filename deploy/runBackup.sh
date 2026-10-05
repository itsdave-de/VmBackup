#!/bin/bash
# runBackup.sh - NAUbackup run on a rotating LUKS-encrypted removable disk (itsdave deployment template)
#
# Flow: find the first attached disk from the list below, open it with the LUKS passphrase from the
# secrets file, mount it, run VmBackup.py, record the target disk state for monitoring, unmount, close.
#
# Install: copy to /root/naubackup/runBackup.sh, adjust DISKS, create /root/naubackup/.secrets
# (see secrets.example, chmod 600) and add to roots crontab, e.g.
#   00 1 * * * /root/naubackup/runBackup.sh >> /root/naubackup/runBackup.log 2>&1
#
# VmBackup.py talks to the local xapi over its unix socket ("local"), so no root password is needed.

NAUBACKUP=/root/naubackup
MOUNTPOINT=/naubackup.store
MAPPER=naubackuptarget
COMPRESS=zstd                      # none | gzip | zstd (zstd needs XCP-ng 8.1+)

# by-id names of the rotation disks (ls -l /dev/disk/by-id/); the first one found is used
DISKS=(usb-WD_My_Passport_XXXX_XXXXXXXXXXXXXXXXXXXXXXXX-0:0-part1
       usb-WD_My_Passport_XXXX_YYYYYYYYYYYYYYYYYYYYYYYY-0:0-part1)

cryptsetup=/usr/sbin/cryptsetup
target=false

. "$NAUBACKUP/.secrets" || { echo "$(date '+%F %T') no $NAUBACKUP/.secrets, aborting"; exit 2; }
[ -n "$lukspass" ] || { echo "$(date '+%F %T') lukspass missing in $NAUBACKUP/.secrets, aborting"; exit 2; }
mkdir -p "$MOUNTPOINT"

if awk -v m="$MOUNTPOINT" '$2==m{found=1} END{exit !found}' /etc/mtab; then
    echo "$(date '+%F %T') $MOUNTPOINT is still mounted, aborting."
    echo "Make sure no backup is running, then: umount $MOUNTPOINT && $cryptsetup luksClose $MAPPER"
    exit 2
fi

for id in "${DISKS[@]}"; do
    if [ -L "/dev/disk/by-id/$id" ]; then
        echo "$(date '+%F %T') backup target $id found."
        target="/dev/disk/by-id/$id"
        break
    fi
done
if [ "$target" = false ]; then
    echo "$(date '+%F %T') no backup disk attached, aborting."
    exit 2
fi

echo -n "$lukspass" | $cryptsetup luksOpen "$target" "$MAPPER" -d - || { echo "luksOpen failed"; exit 2; }
mount "/dev/mapper/$MAPPER" "$MOUNTPOINT" || { $cryptsetup luksClose "$MAPPER"; echo "mount failed"; exit 2; }

"$NAUBACKUP/VmBackup.py" local "$NAUBACKUP/VmBackup.cfg" compress=$COMPRESS
rc=$?

# target disk state for check_naubackup and the JSON report (disk still mounted here)
DF=$(/bin/df -k "$MOUNTPOINT" 2>/dev/null | awk 'NR==2{print $2, $3, $4, $5+0}')
{
  echo "target_id=$id"
  echo "target_luks_uuid=$(/sbin/blkid -s UUID -o value "$(readlink -f "$target")" 2>/dev/null)"
  PDEV=$(/bin/lsblk -no pkname "$(readlink -f "$target")" 2>/dev/null | head -1)
  [ -z "$PDEV" ] && PDEV=$(basename "$(readlink -f "$target")")
  SER=$(/usr/sbin/smartctl -i -d sat "/dev/$PDEV" 2>/dev/null | sed -n 's/^Serial Number:[ ]*//p')
  [ -z "$SER" ] && SER=$(/usr/sbin/smartctl -i "/dev/$PDEV" 2>/dev/null | sed -n 's/^Serial Number:[ ]*//p')
  echo "target_serial=$SER"
  echo "disk_size_kb=$(echo "$DF" | cut -d' ' -f1)"
  echo "disk_used_kb=$(echo "$DF" | cut -d' ' -f2)"
  echo "disk_avail_kb=$(echo "$DF" | cut -d' ' -f3)"
  echo "disk_used_pct=$(echo "$DF" | cut -d' ' -f4)"
  echo "captured_epoch=$(date +%s)"
} > "$NAUBACKUP/target_state" 2>/dev/null

umount "$MOUNTPOINT"
$cryptsetup luksClose "$MAPPER"
exit $rc
