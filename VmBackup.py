#!/usr/bin/env python3
# V4.0.0-itsdave October 2026
#
# Copyright (C) 2018  Northern Arizona University
# Copyright (C) 2026  itsdave GmbH (Python-3-Port, zstd, Secrets, API-Reporting)
#
# Initial Authors:
# Douglas Pace
# Tobias Kreidl
#
# With external contributions gratefully made by:
# @philippmk -
# @ilium007 -
# @HqWisen -
# @JHag6694 -
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# Title: NAUbackup/VmBackup - a XenServer/XCP-ng vm-export & vdi-export Backup Script
# Package Contents: README.md, VmBackup.py (this file), example.cfg, deploy/
# Version History
# - v4.0.0-itsdave 2026/10/05 Python 3 (3.6+, XCP-ng 8.x dom0), compress=none|gzip|zstd,
#         XenAPI over the local unix socket (password "local", no root password
#         needed on the host), SMTP credentials and API token from a secrets
#         file instead of the script, mail settings in the config file,
#         JSON report (schema naubackup-v1) posted to the itsdave backup API,
#         exit code 2 on errors / 1 on warnings, output flushed line by line.
# - v3.22.itsdave 2018/07/30 Added function to exclude Disks starting with [NOBAK], like Xen Orchestra does
# - v3.25 2019/08/07 Reconcile XenAPI.Session to be compatible
#         with XenServer 6.X - 8.X releases, alert users in README file that
#         session.xenapi.VM.get_by_name_label also returns name_labels
#         of templates and hence should be avoided for VMs.
# - v3.24 2019/04/19 Fix lingering duplicate VM issues
# - v3.23 2018/06/13 Add preview check and execution check for duplicate VM
#         names (potentially conflicting with snapshots),
#         Add pre_clean option to delete oldest backups beforehand,
#         fix subtle bug in pre-removing non-existing VMs from exclude list,
#         add hostname to email subject line
# - v3.22 2017/11/11 Add full VM metadata dump to XML file to replace VM
#         metadata backup that could fail if special characters encountered
#         Added name_description UNICODE fix. (2018-Mar-20)
# - v3.21 2017/09/29 Fix "except socket.error" syntax to also work with older
#         python version in XenServer 6.X
# - v3.2  2017/09/12 Fix wildcard handling and excludes for both VM and VDI
#         cases, add email retries
# - v3.1  2016/11/26 Added regexp include/exclude syntax for selecting VMs,
#         checking writability of backup directory, SMTP TLS email option,
#         define DEFAULT_STATUS_LOG parameter
# - v3.0  2016/01/20 Added vdi-export for VMs with too many/large disks for
#         vm-export
# - v2.1  2014/08/22 Added email status option
# - v2.0  2014/04/09 New VmBackup version (supersedes all previous NAUbackup
#         versions)

# ** DO NOT RUN THIS SCRIPT UNLESS YOU ARE COMFORTABLE WITH THESE ACTIONS. **
# => To accomplish the vm backup this script uses the following xe commands
#   vm-export:  (a) vm-snapshot, (b) template-param-set, (c) vm-export, (d) vm-uninstall on vm-snapshot
#   vdi-export: (a) vdi-snapshot, (b) vdi-param-set, (c) vdi-export, (d) vdi-destroy on vdi-snapshot

# See README for usage and installation documentation.
# See example.cfg for config file example usage.

# Usage w/ vm name for single vm backup, which runs vm-export by default:
#    ./VmBackup.py <password|local> <vm-name>

# Usage w/ config file for multiple vm backups, where you can specify either vm-export or vdi-export:
#    ./VmBackup.py <password|local> <config-file-path>

import sys, time, os, datetime, subprocess, re, shutil, smtplib, base64, socket, json, uuid as uuidlib
import urllib.request, urllib.error
from email.mime.text import MIMEText
from subprocess import PIPE
from subprocess import STDOUT

import XenAPI

VERSION = 'V4.0.0-itsdave'
REPORT_SCHEMA = 'naubackup-v1'

############################# HARD CODED DEFAULTS
# modify these hard coded default values, only used if not specified in config file
DEFAULT_POOL_DB_BACKUP = 0
DEFAULT_MAX_BACKUPS = 4
DEFAULT_VDI_EXPORT_FORMAT = 'raw' # xe vdi-export options: 'raw' or 'vhd'
DEFAULT_BACKUP_DIR = '/snapshots/BACKUPS'
## DEFAULT_BACKUP_DIR = '\snapshots\BACKUPS' # alt for CIFS mounts
# note - some NAS file servers may fail with ':', so change to your desired format
BACKUP_DIR_PATTERN = '%s/backup-%04d-%02d-%02d-(%02d:%02d:%02d)'
DEFAULT_STATUS_LOG = 'status.log'
DEFAULT_COMPRESS = 'none'          # none | gzip | zstd  (zstd needs XCP-ng 8.1+ / XenServer 8.x)
DEFAULT_SECRETS_FILE = '/root/naubackup/.secrets'
DEFAULT_MAIL_SMTP_PORT = 25
DEFAULT_MAIL_MODE = 'always'       # always | problems | never  (only if mail_to is set)
DEFAULT_API_URL = 'https://backupapi.itsdave.de/api/v1'

############################# OPTIONAL (legacy fallbacks, prefer the config file keys mail_to / mail_from / mail_smtp_server)
MAIL_TO_ADDR = ''
MAIL_FROM_ADDR = ''
MAIL_SMTP_SERVER = ''

config = {}
secrets = {}
all_vms = []
expected_keys = ['pool_db_backup', 'max_backups', 'backup_dir', 'status_log', 'vdi_export_format', 'vm-export', 'vdi-export', 'exclude',
                 'compress', 'mail_to', 'mail_from', 'mail_smtp_server', 'mail_smtp_port', 'mail_mode',
                 'api_url', 'api_hostname', 'api_report']
message = ''
xe_path = '/opt/xensource/bin'

# collected for the JSON report (schema naubackup-v1)
report = {'vms': [], 'pool_metadata': {'enabled': False, 'success': None}}

def main(session):

    success_cnt = 0
    warning_cnt = 0
    error_cnt = 0
    run_begin = datetime.datetime.now()

    server_name = os.uname()[1].split('.')[0]
    if config_specified:
        status_log_begin(server_name)

    log('===========================')
    log('VmBackup %s running on %s ...' % (VERSION, server_name))

    log('===========================')
    log('Check if backup directory %s is writable ...' % config['backup_dir'])
    touchfile = os.path.join(config['backup_dir'], "00VMbackupWriteTest")

    cmd = '/bin/touch "%s"' % touchfile
    log(cmd)
    res = run(cmd)
    if not res:
        log('ERROR failed to write to backup directory area - FATAL ERROR')
        sys.exit(2)
    else:
        cmd = '/bin/rm -f "%s"' % touchfile
        res = run(cmd)
        log('Success: backup directory area is writable')

    log('===========================')
    df_snapshots('Space before backups: df -Th %s' % config['backup_dir'])

    if int(config['pool_db_backup']):
        log('*** begin backup_pool_metadata ***')
        report['pool_metadata']['enabled'] = True
        if not backup_pool_metadata(server_name):
            error_cnt += 1
            report['pool_metadata']['success'] = False
        else:
            report['pool_metadata']['success'] = True

    ######################################################################
    # Iterate through all vdi-export= in cfg
    log('************ vdi-export= ***************')
    for vm_parm in config['vdi-export']:
        log('*** vdi-export begin %s' % vm_parm)
        beginTime = datetime.datetime.now()
        this_status = 'success'

        # get values from vdi-export=
        vm_name = get_vm_name(vm_parm)
        vm_max_backups = get_vm_max_backups(vm_parm)
        log('vdi-export - vm_name: %s max_backups: %s' % (vm_name, vm_max_backups))
        vm_report = report_vm_begin(vm_name, 'vdi-export', vm_max_backups, beginTime)

        if config_specified:
            status_log_vdi_export_begin(server_name, '%s' % vm_name)

        # verify vm_name exists with only one instance for this name
        #  returns error-message or vm_object if success
        vm_object = verify_vm_name(vm_name)
        if 'ERROR' in vm_object:
            log('verify_vm_name: %s' % vm_object)
            if config_specified:
                status_log_vdi_export_end(server_name, 'ERROR verify_vm_name %s' % vm_name)
            error_cnt += 1
            report_vm_end(vm_report, 'error', 'verify_vm_name')
            # next vm
            continue

        vm_backup_dir = os.path.join(config['backup_dir'], vm_name)
        # cleanup any old unsuccessful backups and create new full_backup_dir
        full_backup_dir = process_backup_dir(vm_backup_dir)

        # gather_vm_meta produces status: empty or warning-message
        #   and globals: vm_uuid, xvda_uuid, xvda_uuid
        #   => now only need: vm_uuid
        #   since all VM metadta go into an XML file
        vm_meta_status = gather_vm_meta(vm_object, full_backup_dir)
        if vm_meta_status != '':
            log('WARNING gather_vm_meta: %s' % vm_meta_status)
            this_status = 'warning'
            # non-fatal - finsh processing for this vm

        # vdi-export only uses xvda_uuid, xvda_uuid
        if xvda_uuid == '':
            log('ERROR gather_vm_meta has no xvda-uuid')
            if config_specified:
                status_log_vdi_export_end(server_name, 'ERROR xvda-uuid not found %s' % vm_name)
            error_cnt += 1
            report_vm_end(vm_report, 'error', 'xvda-uuid not found')
            # next vm
            continue
        if xvda_name_label == '':
            log('ERROR gather_vm_meta has no xvda-name-label')
            if config_specified:
                status_log_vdi_export_end(server_name, 'ERROR xvda-name-label not found %s' % vm_name)
            error_cnt += 1
            report_vm_end(vm_report, 'error', 'xvda-name-label not found')
            # next vm
            continue

        # -----------------------------------------
        # --- begin vdi-export command sequence ---
        log ('*** vdi-export begin xe command sequence')
        # is vm currently running?
        cmd = '%s/xe vm-list name-label="%s" params=power-state | /bin/grep running' % (xe_path, vm_name)
        if run_log_out_wait_rc(cmd) == 0:
            log ('vm is running')
            vm_report['power_state'] = 'running'
        else:
            log ('vm is NOT running')
            vm_report['power_state'] = 'halted'

        # list the vdi we will backup
        cmd = '%s/xe vdi-list uuid=%s' % (xe_path, xvda_uuid)
        log('1.cmd: %s' % cmd)
        if run_log_out_wait_rc(cmd) != 0:
            log('ERROR %s' % cmd)
            if config_specified:
                status_log_vdi_export_end(server_name, 'VDI-LIST-FAIL %s' % vm_name)
            error_cnt += 1
            report_vm_end(vm_report, 'error', 'VDI-LIST-FAIL')
            # next vm
            continue

        # check for old vdi-snapshot for this xvda
        snap_vdi_name_label = 'SNAP_%s_%s' % (vm_name, xvda_name_label)
        # replace all spaces with '-'
        snap_vdi_name_label = re.sub(r' ', r'-', snap_vdi_name_label)
        log ('check for prev-vdi-snapshot: %s' % snap_vdi_name_label)
        cmd = "%s/xe vdi-list name-label='%s' params=uuid | /bin/awk -F': ' '{print $2}' | /bin/grep '-'" % (xe_path, snap_vdi_name_label)
        old_snap_vdi_uuid = run_get_lastline(cmd)
        if old_snap_vdi_uuid != '':
            log ('cleanup old-snap-vdi-uuid: %s' % old_snap_vdi_uuid)
            # vdi-destroy old vdi-snapshot
            cmd = '%s/xe vdi-destroy uuid=%s' % (xe_path, old_snap_vdi_uuid)
            log('cmd: %s' % cmd)
            if run_log_out_wait_rc(cmd) != 0:
                log('WARNING %s' % cmd)
                this_status = 'warning'
                # non-fatal - finish processing for this vm

        # === pre_cleanup code goes in here ===
        if pre_clean:
           pre_cleanup ( vm_backup_dir, vm_max_backups)

        # take a vdi-snapshot of this vm
        cmd = '%s/xe vdi-snapshot uuid=%s' % (xe_path, xvda_uuid)
        log('2.cmd: %s' % cmd)
        snap_vdi_uuid = run_get_lastline(cmd)
        log ('snap-uuid: %s' % snap_vdi_uuid)
        if snap_vdi_uuid == '':
            log('ERROR %s' % cmd)
            if config_specified:
                status_log_vdi_export_end(server_name, 'VDI-SNAPSHOT-FAIL %s' % vm_name)
            error_cnt += 1
            report_vm_end(vm_report, 'error', 'VDI-SNAPSHOT-FAIL')
            # next vm
            continue

        # change vdi-snapshot to unique name-label for easy id and cleanup
        cmd = '%s/xe vdi-param-set uuid=%s name-label="%s"' % (xe_path, snap_vdi_uuid, snap_vdi_name_label)
        log('3.cmd: %s' % cmd)
        if run_log_out_wait_rc(cmd) != 0:
            log('ERROR %s' % cmd)
            if config_specified:
                status_log_vdi_export_end(server_name, 'VDI-PARAM-SET-FAIL %s' % vm_name)
            error_cnt += 1
            report_vm_end(vm_report, 'error', 'VDI-PARAM-SET-FAIL')
            # next vm
            continue

        # actual-backup: vdi-export vdi-snapshot
        cmd = '%s/xe vdi-export format=%s uuid=%s' % (xe_path, config['vdi_export_format'], snap_vdi_uuid)
        full_path_backup_file = os.path.join(full_backup_dir, vm_name + '.%s' % config['vdi_export_format'])
        cmd = '%s filename="%s"' % (cmd, full_path_backup_file)
        log('4.cmd: %s' % cmd)
        if run_log_out_wait_rc(cmd) == 0:
            log('vdi-export success')
        else:
            log('ERROR %s' % cmd)
            if config_specified:
                status_log_vdi_export_end(server_name, 'VDI-EXPORT-FAIL %s' % vm_name)
            error_cnt += 1
            report_vm_end(vm_report, 'error', 'VDI-EXPORT-FAIL')
            # next vm
            continue

        # cleanup: vdi-destroy vdi-snapshot
        cmd = '%s/xe vdi-destroy uuid=%s' % (xe_path, snap_vdi_uuid)
        log('5.cmd: %s' % cmd)
        if run_log_out_wait_rc(cmd) != 0:
            log('WARNING %s' % cmd)
            this_status = 'warning'
            # non-fatal - finsh processing for this vm

        log ('*** vdi-export end')
        # --- end vdi-export command sequence ---
        # ---------------------------------------

        elapseTime = datetime.datetime.now() - beginTime
        backup_file_bytes = os.path.getsize(full_path_backup_file)
        backup_file_size = backup_file_bytes // (1024 * 1024 * 1024)
        final_cleanup( full_path_backup_file, backup_file_size, full_backup_dir, vm_backup_dir, vm_max_backups)

        if not check_all_backups_success(vm_backup_dir):
            log('WARNING cleanup needed - not all backup history is successful')
            this_status = 'warning'

        vm_report['file'] = full_path_backup_file
        vm_report['size_bytes'] = backup_file_bytes
        vm_report['copies'] = count_successful_backups(vm_backup_dir)
        elapse_min = elapseTime.seconds // 60
        if (this_status == 'success'):
            success_cnt += 1
            log('VmBackup vdi-export %s - ***Success*** t:%s' % (vm_name, elapse_min))
            if config_specified:
                status_log_vdi_export_end(server_name, 'SUCCESS %s,elapse:%s size:%sG' % (vm_name, elapse_min, backup_file_size))
            report_vm_end(vm_report, 'success', 'SUCCESS')

        elif (this_status == 'warning'):
            warning_cnt += 1
            log('VmBackup vdi-export %s - ***WARNING*** t:%s' % (vm_name, elapse_min))
            if config_specified:
                status_log_vdi_export_end(server_name, 'WARNING %s,elapse:%s size:%sG' % (vm_name, elapse_min, backup_file_size))
            report_vm_end(vm_report, 'warning', 'WARNING')

        else:
            # this should never occur since all errors do a continue on to the next vm_name
            error_cnt += 1
            log('VmBackup vdi-export %s - +++ERROR-INTERNAL+++ t:%s' % (vm_name, elapse_min))
            if config_specified:
                status_log_vdi_export_end(server_name, 'ERROR-INTERNAL %s,elapse:%s size:%sG' % (vm_name, elapse_min, backup_file_size))
            report_vm_end(vm_report, 'error', 'ERROR-INTERNAL')

    # end of for vm_parm in config['vdi-export']:
    ######################################################################


    ######################################################################
    # Iterate through all vm-export= in cfg
    log('************ vm-export= ***************')
    for vm_parm in config['vm-export']:
        log('*** vm-export begin %s' % vm_parm)
        beginTime = datetime.datetime.now()
        this_status = 'success'

        # get values from vdi-export=
        vm_name = get_vm_name(vm_parm)
        vm_max_backups = get_vm_max_backups(vm_parm)
        log('vm-export - vm_name: %s max_backups: %s' % (vm_name, vm_max_backups))
        vm_report = report_vm_begin(vm_name, 'vm-export', vm_max_backups, beginTime)

        if config_specified:
            status_log_vm_export_begin(server_name, '%s' % vm_name)

        vm_object = verify_vm_name(vm_name)
        if 'ERROR' in vm_object:
            log('verify_vm_name: %s' % vm_object)
            if config_specified:
                status_log_vm_export_end(server_name, 'ERROR verify_vm_name %s' % vm_name)
            error_cnt += 1
            report_vm_end(vm_report, 'error', 'verify_vm_name')
            # next vm
            continue

        vm_backup_dir = os.path.join(config['backup_dir'], vm_name)
        # cleanup any old unsuccessful backups and create new full_backup_dir
        full_backup_dir = process_backup_dir(vm_backup_dir)

        # gather_vm_meta produces status: empty or warning-message
        #   and globals: vm_uuid, xvda_uuid, xvda_uuid
        vm_meta_status = gather_vm_meta(vm_object, full_backup_dir)
        if vm_meta_status != '':
            log('WARNING gather_vm_meta: %s' % vm_meta_status)
            this_status = 'warning'
            # non-fatal - finsh processing for this vm
        # vm-export only uses vm_uuid
        if vm_uuid == '':
            log('ERROR gather_vm_meta has no vm-uuid')
            if config_specified:
                status_log_vm_export_end(server_name, 'ERROR vm-uuid not found %s' % vm_name)
            error_cnt += 1
            report_vm_end(vm_report, 'error', 'vm-uuid not found')
            # next vm
            continue
        vm_report['uuid'] = vm_uuid

        # ----------------------------------------
        # --- begin vm-export command sequence ---
        log ('*** vm-export begin xe command sequence')
        # is vm currently running?
        cmd = '%s/xe vm-list name-label="%s" params=power-state | /bin/grep running' % (xe_path, vm_name)
        if run_log_out_wait_rc(cmd) == 0:
            log ('vm is running')
            vm_report['power_state'] = 'running'
        else:
            log ('vm is NOT running')
            vm_report['power_state'] = 'halted'

        # check for old vm-snapshot for this vm
        snap_name = 'RESTORE_%s' % vm_name
        log ('check for prev-vm-snapshot: %s' % snap_name)
        cmd = "%s/xe vm-list name-label='%s' params=uuid | /bin/awk -F': ' '{print $2}' | /bin/grep '-'" % (xe_path, snap_name)
        old_snap_vm_uuid = run_get_lastline(cmd)
        if old_snap_vm_uuid != '':
            log ('cleanup old-snap-vm-uuid: %s' % old_snap_vm_uuid)
            # vm-uninstall old vm-snapshot
            cmd = '%s/xe vm-uninstall uuid=%s force=true' % (xe_path, old_snap_vm_uuid)
            log('cmd: %s' % cmd)
            if run_log_out_wait_rc(cmd) != 0:
                log('WARNING-ERROR %s' % cmd)
                this_status = 'warning'
                if config_specified:
                    status_log_vm_export_end(server_name, 'VM-UNINSTALL-FAIL-1 %s' % vm_name)
                # non-fatal - finsh processing for this vm

        # === pre_cleanup code goes in here ===
        if pre_clean:
           pre_cleanup (vm_backup_dir, vm_max_backups)

        # take a vm-snapshot of this vm
        cmd = '%s/xe vm-snapshot vm=%s new-name-label="%s"' % (xe_path, vm_uuid, snap_name)
        log('1.cmd: %s' % cmd)
        snap_vm_uuid = run_get_lastline(cmd)
        log ('snap-uuid: %s' % snap_vm_uuid)
        if snap_vm_uuid == '':
            log('ERROR %s' % cmd)
            if config_specified:
                status_log_vm_export_end(server_name, 'SNAPSHOT-FAIL %s' % vm_name)
            error_cnt += 1
            report_vm_end(vm_report, 'error', 'SNAPSHOT-FAIL')
            # next vm
            continue

        # change vm-snapshot so that it can be referenced by vm-export
        cmd = '%s/xe template-param-set is-a-template=false ha-always-run=false uuid=%s' % (xe_path, snap_vm_uuid)
        log('2.cmd: %s' % cmd)
        if run_log_out_wait_rc(cmd) != 0:
            log('ERROR %s' % cmd)
            if config_specified:
                status_log_vm_export_end(server_name, 'TEMPLATE-PARAM-SET-FAIL %s' % vm_name)
            error_cnt += 1
            report_vm_end(vm_report, 'error', 'TEMPLATE-PARAM-SET-FAIL')
            # next vm
            continue

        # exclude disks whose VDI name-label starts with [NOBAK] (same convention as Xen Orchestra):
        # the snapshot's VBD and VDI are destroyed before the export, the original VM is untouched.
        vm_report['excluded_disks'] = exclude_nobak_disks(snap_vm_uuid)

        # vm-export vm-snapshot
        cmd = '%s/xe vm-export uuid=%s' % (xe_path, snap_vm_uuid)
        if compress == 'zstd':
            full_path_backup_file = os.path.join(full_backup_dir, vm_name + '.xva.zst')
            cmd = '%s filename="%s" compress=zstd' % (cmd, full_path_backup_file)
        elif compress == 'gzip':
            full_path_backup_file = os.path.join(full_backup_dir, vm_name + '.xva.gz')
            cmd = '%s filename="%s" compress=true' % (cmd, full_path_backup_file)
        else:
            full_path_backup_file = os.path.join(full_backup_dir, vm_name + '.xva')
            cmd = '%s filename="%s"' % (cmd, full_path_backup_file)
        log('3.cmd: %s' % cmd)
        if run_log_out_wait_rc(cmd) == 0:
            log('vm-export success')
        else:
            log('ERROR %s' % cmd)
            if config_specified:
                status_log_vm_export_end(server_name, 'VM-EXPORT-FAIL %s' % vm_name)
            error_cnt += 1
            report_vm_end(vm_report, 'error', 'VM-EXPORT-FAIL')
            # next vm
            continue

        # vm-uninstall vm-snapshot
        cmd = '%s/xe vm-uninstall uuid=%s force=true' % (xe_path, snap_vm_uuid)
        log('4.cmd: %s' % cmd)
        if run_log_out_wait_rc(cmd) != 0:
            log('WARNING %s' % cmd)
            this_status = 'warning'
            # non-fatal - finsh processing for this vm

        log ('*** vm-export end')
        # --- end vm-export command sequence ---
        # ----------------------------------------

        elapseTime = datetime.datetime.now() - beginTime
        backup_file_bytes = os.path.getsize(full_path_backup_file)
        backup_file_size = backup_file_bytes // (1024 * 1024 * 1024)
        final_cleanup( full_path_backup_file, backup_file_size, full_backup_dir, vm_backup_dir, vm_max_backups)

        if not check_all_backups_success(vm_backup_dir):
            log('WARNING cleanup needed - not all backup history is successful')
            this_status = 'warning'

        vm_report['file'] = full_path_backup_file
        vm_report['size_bytes'] = backup_file_bytes
        vm_report['copies'] = count_successful_backups(vm_backup_dir)
        elapse_min = elapseTime.seconds // 60
        if (this_status == 'success'):
            success_cnt += 1
            log('VmBackup vm-export %s - ***Success*** t:%s' % (vm_name, elapse_min))
            if config_specified:
                status_log_vm_export_end(server_name, 'SUCCESS %s,elapse:%s size:%sG' % (vm_name, elapse_min, backup_file_size))
            report_vm_end(vm_report, 'success', 'SUCCESS')

        elif (this_status == 'warning'):
            warning_cnt += 1
            log('VmBackup vm-export %s - ***WARNING*** t:%s' % (vm_name, elapse_min))
            if config_specified:
                status_log_vm_export_end(server_name, 'WARNING %s,elapse:%s size:%sG' % (vm_name, elapse_min, backup_file_size))
            report_vm_end(vm_report, 'warning', 'WARNING')

        else:
            # this should never occur since all errors do a continue on to the next vm_name
            error_cnt += 1
            log('VmBackup vm-export %s - +++ERROR-INTERNAL+++ t:%s' % (vm_name, elapse_min))
            if config_specified:
                status_log_vm_export_end(server_name, 'ERROR-INTERNAL %s,elapse:%s size:%sG' % (vm_name, elapse_min, backup_file_size))
            report_vm_end(vm_report, 'error', 'ERROR-INTERNAL')

    # end of for vm_parm in config['vm-export']:
    ######################################################################

    log('===========================')
    df_snapshots('Space status: df -Th %s' % config['backup_dir'])

    # gather a final VmBackup.py status
    summary = 'S:%s W:%s E:%s' % (success_cnt, warning_cnt, error_cnt)
    status_log = config['status_log']
    if (error_cnt > 0):
        overall = 'error'
        if config_specified:
            status_log_end(server_name, 'ERROR,%s' % summary)
        log('VmBackup ended - **ERRORS DETECTED** - %s' % summary)
    elif (warning_cnt > 0):
        overall = 'warning'
        if config_specified:
            status_log_end(server_name, 'WARNING,%s' % summary)
        log('VmBackup ended - **WARNING(s)** - %s' % summary)
    else:
        overall = 'success'
        if config_specified:
            status_log_end(server_name, 'SUCCESS,%s' % summary)
        log('VmBackup ended - Success - %s' % summary)

    # report to the itsdave backup API (schema naubackup-v1) and by mail; neither may change the result
    run_end = datetime.datetime.now()
    try:
        report_finish(server_name, run_begin, run_end, overall, success_cnt, warning_cnt, error_cnt)
    except Exception as e:
        log('WARNING report could not be built or sent: %s' % e)

    if mail_wanted(overall):
        subject = {'error': 'ERROR', 'warning': 'WARNING', 'success': 'Success'}[overall]
        send_email(mail_setting('mail_to', MAIL_TO_ADDR), '%s %s VmBackup.py' % (subject, os.uname()[1]), status_log)
        if config_specified:
            open('%s' % status_log, 'w').close() # trunc status log after email

    return {'error': 2, 'warning': 1, 'success': 0}[overall]

    # done with main()
    ######################################################################

############################# report (naubackup-v1)

def report_vm_begin(vm_name, mode, vm_max_backups, begin_time):
    entry = {
        'name': vm_name,
        'mode': mode,
        'max_backups': vm_max_backups,
        'started_at': begin_time.isoformat(timespec='seconds'),
        'ended_at': None,
        'duration_sec': None,
        'status': 'running',
        'message': '',
        'file': None,
        'size_bytes': None,
        'copies': None,
    }
    report['vms'].append(entry)
    return entry

def report_vm_end(entry, status, text):
    end = datetime.datetime.now()
    entry['status'] = status
    entry['message'] = text
    entry['ended_at'] = end.isoformat(timespec='seconds')
    try:
        begin = datetime.datetime.strptime(entry['started_at'], '%Y-%m-%dT%H:%M:%S')
        entry['duration_sec'] = int((end - begin).total_seconds())
    except ValueError:
        entry['duration_sec'] = None

def count_successful_backups(path):
    # how many restorable copies the target holds for this VM
    try:
        dirs = os.listdir(path)
    except OSError:
        return None
    cnt = 0
    for d in dirs:
        for marker in ('success', 'success_restore', 'success_compress', 'success_compressing'):
            if os.path.exists(os.path.join(path, d, marker)):
                cnt += 1
                break
    return cnt

def target_info(path):
    info = {'backup_dir': path}
    try:
        st = os.statvfs(path)
        size = st.f_blocks * st.f_frsize
        avail = st.f_bavail * st.f_frsize
        used = size - st.f_bfree * st.f_frsize
        info.update({'size_bytes': size, 'used_bytes': used, 'avail_bytes': avail,
                     'used_pct': round(used * 100.0 / size, 1) if size else None})
    except OSError as e:
        info['error'] = str(e)
    # device / filesystem from df
    try:
        out = subprocess.check_output(['/bin/df', '-T', path], universal_newlines=True, stderr=subprocess.STDOUT).splitlines()
        if len(out) >= 2:
            fields = out[1].split()
            info['device'] = fields[0]
            info['fstype'] = fields[1]
            info['mountpoint'] = fields[-1]
    except (OSError, subprocess.CalledProcessError):
        pass
    # target_state written by runBackup.sh (removable disk identity), if present
    state_file = os.path.join(os.path.dirname(os.path.abspath(config['status_log'])), 'target_state')
    if os.path.exists(state_file):
        state = {}
        with open(state_file) as f:
            for line in f:
                if '=' in line:
                    k, v = line.rstrip('\n').split('=', 1)
                    state[k.strip()] = v.strip()
        info['target_state'] = state
    return info

def host_info(server_name):
    info = {'name': server_name, 'fqdn': os.uname()[1], 'product': None, 'version': None, 'pool_master': None}
    try:
        with open('/etc/xensource-inventory') as f:
            for line in f:
                if line.startswith('PRODUCT_BRAND='):
                    info['product'] = line.split('=', 1)[1].strip().strip("'")
                if line.startswith('PRODUCT_VERSION='):
                    info['version'] = line.split('=', 1)[1].strip().strip("'")
    except OSError:
        pass
    try:
        info['pool_master'] = is_xe_master()
    except Exception:
        pass
    return info

def report_finish(server_name, run_begin, run_end, overall, success_cnt, warning_cnt, error_cnt):
    data = {
        'schema': REPORT_SCHEMA,
        'backup_type': REPORT_SCHEMA,
        'generator': 'VmBackup.py %s' % VERSION,
        'host': host_info(server_name),
        'run': {
            'started_at': run_begin.isoformat(timespec='seconds'),
            'ended_at': run_end.isoformat(timespec='seconds'),
            'duration_sec': int((run_end - run_begin).total_seconds()),
            'status': overall,
            'success_count': success_cnt,
            'warning_count': warning_cnt,
            'error_count': error_cnt,
            'config_file': cfg_file if config_specified else None,
            'compress': compress,
            'vm_count_configured': len(config['vm-export']) + len(config['vdi-export']),
        },
        'target': target_info(config['backup_dir']),
        'pool_metadata': report['pool_metadata'],
        'vms': report['vms'],
    }
    report_file = os.path.join(os.path.dirname(os.path.abspath(config['status_log'])), 'last_report.json')
    try:
        with open(report_file, 'w') as f:
            json.dump(data, f, indent=2, sort_keys=True)
        log('report written: %s' % report_file)
    except OSError as e:
        log('WARNING could not write %s: %s' % (report_file, e))

    if not api_report_wanted():
        return
    token = secrets.get('api_token', '')
    if not token:
        log('WARNING api_report requested but no api_token in secrets file %s' % secrets_file)
        return
    api_url = (config_value('api_url') or DEFAULT_API_URL).rstrip('/')
    hostname = config_value('api_hostname') or os.uname()[1]
    ok, answer = post_report(api_url + '/backup', token, hostname, data)
    if ok:
        log('report sent to %s as %s: %s' % (api_url, hostname, answer[:200]))
    else:
        log('WARNING report NOT sent to %s: %s' % (api_url, answer[:300]))

def api_report_wanted():
    value = config_value('api_report').lower()
    if value in ('false', 'no', '0', 'off'):
        return False
    if value in ('true', 'yes', '1', 'on'):
        return True
    # default: report when a token is configured
    return bool(secrets.get('api_token'))

def post_report(url, token, hostname, data):
    # multipart/form-data: hostname, backup_type, backuplog (JSON file) - the format the itsdave backup API expects
    boundary = '----NAUbackup%s' % uuidlib.uuid4().hex[:16]
    body_json = json.dumps(data, indent=2, sort_keys=True).encode('utf-8')
    parts = []
    parts.append(('--%s' % boundary).encode())
    parts.append(b'Content-Disposition: form-data; name="hostname"')
    parts.append(b'')
    parts.append(hostname.encode('utf-8'))
    parts.append(('--%s' % boundary).encode())
    parts.append(b'Content-Disposition: form-data; name="backup_type"')
    parts.append(b'')
    parts.append(REPORT_SCHEMA.encode())
    parts.append(('--%s' % boundary).encode())
    parts.append(b'Content-Disposition: form-data; name="backuplog"; filename="naubackup-report.json"')
    parts.append(b'Content-Type: application/json')
    parts.append(b'')
    parts.append(body_json)
    parts.append(('--%s--' % boundary).encode())
    parts.append(b'')
    body = b'\r\n'.join(parts)
    headers = {'Content-Type': 'multipart/form-data; boundary=%s' % boundary,
               'Authorization': 'Bearer %s' % token,
               'User-Agent': 'VmBackup.py %s' % VERSION}
    last = ''
    for attempt in range(3):
        try:
            req = urllib.request.Request(url, data=body, headers=headers, method='POST')
            with urllib.request.urlopen(req, timeout=30) as resp:
                answer = resp.read().decode('utf-8', 'replace')
                if resp.status in (200, 201):
                    return True, answer
                last = 'HTTP %s: %s' % (resp.status, answer)
        except urllib.error.HTTPError as e:
            last = 'HTTP %s: %s' % (e.code, e.read().decode('utf-8', 'replace')[:200])
            if 400 <= e.code < 500:
                break  # not going to get better by retrying
        except (urllib.error.URLError, socket.error) as e:
            last = str(e)
        time.sleep(5)
    return False, last

############################# [NOBAK]

def exclude_nobak_disks(snap_vm_uuid):
    cmd = '%s/xe vbd-list vm-uuid=%s params=uuid,vdi-name-label,vdi-uuid' % (xe_path, snap_vm_uuid)
    log('2.5.cmd: %s' % cmd)
    cmdoutput = run_log_out_wait_rc_ret_output(cmd)
    vbds_to_delete = []
    vdis_to_delete = []
    excluded = []
    current_vbd = ''
    current_vdi = ''

    for line in cmdoutput:
        fields = line.split(':', 1)
        if len(fields) < 2:
            continue
        attrib = fields[0].strip()
        value = fields[1].strip()
        if attrib == 'uuid ( RO)':
            current_vbd = value
            continue
        if attrib == 'vdi-uuid ( RO)':
            current_vdi = value
            continue
        if attrib == 'vdi-name-label ( RO)':
            if value.startswith('[NOBAK]'):
                vbds_to_delete.append(current_vbd)
                vdis_to_delete.append(current_vdi)
                excluded.append(value)
        current_vbd = ''
        current_vdi = ''

    if len(vbds_to_delete) == 0:
        log('no VBDs to exclude')
    else:
        log("deleting [NOBAK] VBDs and VDIs from the snapshot:")
        for uuid in vbds_to_delete:
            cmd = '%s/xe vbd-destroy uuid=%s' % (xe_path, uuid)
            if run_log_out_wait_rc(cmd) == 0:
                log('SUCCESS %s' % cmd)
            else:
                log('ERROR %s' % cmd)
        for uuid in vdis_to_delete:
            cmd = '%s/xe vdi-destroy uuid=%s' % (xe_path, uuid)
            if run_log_out_wait_rc(cmd) == 0:
                log('SUCCESS %s' % cmd)
            else:
                log('ERROR %s' % cmd)
    return excluded

############################# helpers (upstream)

def isInt(s):
    try:
        int(s)
        return True
    except ValueError:
        return False

def get_vm_max_backups(vm_parm):
    # get max_backups from optional vm-export=VM-NAME:MAX-BACKUP override
    # NOTE - if not present then return config['max_backups']
    if vm_parm.find(':') == -1:
        return int(config['max_backups'])
    else:
        (vm_name,tmp_max_backups) = vm_parm.split(':')
        tmp_max_backups = int(tmp_max_backups)
        if (tmp_max_backups > 0):
            return tmp_max_backups
        else:
            return int(config['max_backups'])

def is_vm_backups_valid(vm_parm):
    if vm_parm.find(':') == -1:
        # valid since we will use config['max_backups']
        return True
    else:
        # a value has been specified - is it valid?
        (vm_name,tmp_max_backups) = vm_parm.split(':')
        if isInt(tmp_max_backups):
            return int(tmp_max_backups) > 0
        else:
            return False

def get_vm_backups(vm_parm):
    # get max_backups from optional vm-export=VM-NAME:MAX-BACKUP override
    # NOTE - if not present then return empty string '' else return whatever specified after ':'
    if vm_parm.find(':') == -1:
        return ''
    else:
        (vm_name,tmp_max_backups) = vm_parm.split(':')
        return tmp_max_backups

def get_vm_name(vm_parm):
    # get vm_name from optional vm-export=VM-NAME:MAX-BACKUP override
    if (vm_parm.find(':') == -1):
        return vm_parm
    else:
        (tmp_vm_name,tmp_max_backups) = vm_parm.split(':')
        return tmp_vm_name

def verify_vm_name(tmp_vm_name):
    vm = session.xenapi.VM.get_by_name_label(tmp_vm_name)
    vmref = [x for x in session.xenapi.VM.get_by_name_label(tmp_vm_name) if not session.xenapi.VM.get_is_a_snapshot(x)]
    if (len(vmref) > 1):
       log ("ERROR: duplicate VM name found: %s | %s" % (tmp_vm_name, vmref))
       return 'ERROR more than one vm with the name %s' % tmp_vm_name
    elif (len(vm) == 0):
       return 'ERROR no machines found with the name %s' % tmp_vm_name
    return vm[0]

def gather_vm_meta(vm_object, tmp_full_backup_dir):
    global vm_uuid
    global xvda_uuid
    global xvda_name_label
    vm_uuid = ''
    xvda_uuid = ''
    xvda_name_label = ''
    tmp_error = ''

    vm_record = session.xenapi.VM.get_record(vm_object)
    vm_uuid = vm_record['uuid']

    log ('Exporting VM metadata XML info')
    cmd = '%s/xe vm-export metadata=true uuid=%s filename= | tar -xOf - | /usr/bin/xmllint -format - > "%s/vm-metadata.xml"' % (xe_path, vm_uuid, tmp_full_backup_dir)
    if run_log_out_wait_rc(cmd) != 0:
        log('WARNING %s' % cmd)
        # non-fatal - finish processing for this vm

    log ('*** vm-export metadata end')

    # Write metadata files for vdis and vbds.  These end up inside of a DISK- directory.
    log ('Writing disk info')
    vbd_cnt = 0
    for vbd in vm_record['VBDs']:
        log('vbd: %s' % vbd)
        vbd_record = session.xenapi.VBD.get_record(vbd)
        # For each vbd, find out if its a disk
        if vbd_record['type'].lower() != 'disk':
            continue
        vbd_record_device = vbd_record['device']
        if vbd_record_device == '':
            # not normal - flag as warning.
            # this seems to occur on some vms that have not been started in a long while,
            #   after starting the vm this blank condition seems to go away.
            tmp_error += 'empty vbd_record[device] on vbd: %s ' % vbd
            # if device is not available then use counter as a alternate reference
            vbd_cnt += 1
            vbd_record_device = vbd_cnt

        vdi_record = session.xenapi.VDI.get_record(vbd_record['VDI'])
        log('disk: %s - begin' % vdi_record['name_label'])

        # now write out the vbd info.
        device_path = '%s/DISK-%s' % (tmp_full_backup_dir,  vbd_record_device)
        os.mkdir(device_path)
        with open('%s/vbd.cfg' % device_path, 'w') as vbd_out:
            vbd_out.write('userdevice=%s\n' % vbd_record['userdevice'])
            vbd_out.write('bootable=%s\n' % vbd_record['bootable'])
            vbd_out.write('mode=%s\n' % vbd_record['mode'])
            vbd_out.write('type=%s\n' % vbd_record['type'])
            vbd_out.write('unpluggable=%s\n' % vbd_record['unpluggable'])
            vbd_out.write('empty=%s\n' % vbd_record['empty'])
            # get orig uuid for special metadata disaster recovery
            vbd_out.write('orig_uuid=%s\n' % vbd_record['uuid'])
            # other_config and qos stuff is not backed up

        # now write out the vdi info.
        with open('%s/vdi.cfg' % device_path, 'w') as vdi_out:
            vdi_out.write('name_label=%s\n' % vdi_record['name_label'])
            vdi_out.write('name_description=%s\n' % vdi_record['name_description'])
            vdi_out.write('virtual_size=%s\n' % vdi_record['virtual_size'])
            vdi_out.write('type=%s\n' % vdi_record['type'])
            vdi_out.write('sharable=%s\n' % vdi_record['sharable'])
            vdi_out.write('read_only=%s\n' % vdi_record['read_only'])
            # get orig uuid for special metadata disaster recovery
            vdi_out.write('orig_uuid=%s\n' % vdi_record['uuid'])
            sr_uuid = session.xenapi.SR.get_record(vdi_record['SR'])['uuid']
            vdi_out.write('orig_sr_uuid=%s\n' % sr_uuid)
            # other_config and qos stuff is not backed up
        if vbd_record_device == 'xvda':
            xvda_uuid = vdi_record['uuid']
            xvda_name_label = vdi_record['name_label']

    # Write metadata files for vifs.  These are put in VIFs directory
    log ('Writing VIF info')
    for vif in vm_record['VIFs']:
        vif_record = session.xenapi.VIF.get_record(vif)
        log ('Writing VIF: %s' % vif_record['device'])
        device_path = '%s/VIFs' % tmp_full_backup_dir
        if (not os.path.exists(device_path)):
            os.mkdir(device_path)
        with open('%s/vif-%s.cfg' % (device_path, vif_record['device']), 'w') as vif_out:
            vif_out.write('device=%s\n' % vif_record['device'])
            network_name = session.xenapi.network.get_record(vif_record['network'])['name_label']
            vif_out.write('network_name_label=%s\n' % network_name)
            vif_out.write('MTU=%s\n' % vif_record['MTU'])
            vif_out.write('MAC=%s\n' % vif_record['MAC'])
            vif_out.write('other_config=%s\n' % vif_record['other_config'])
            vif_out.write('orig_uuid=%s\n' % vif_record['uuid'])

    return tmp_error

def final_cleanup( tmp_full_path_backup_file, tmp_backup_file_size, tmp_full_backup_dir, tmp_vm_backup_dir, tmp_vm_max_backups):
    # mark this a successful backup, note: this will 'touch' a file named 'success'
    # if backup size is greater than 60G, then nfs server side compression occurs
    if tmp_backup_file_size > 60:
        log('*** LARGE FILE > 60G: %s : %sG' % (tmp_full_path_backup_file, tmp_backup_file_size))
        # forced compression via background gzip (requires nfs server side script)
        open('%s/success_compress' % tmp_full_backup_dir, 'w').close()
        log('*** success_compress: %s : %sG' % (tmp_full_path_backup_file, tmp_backup_file_size))
    else:
        open('%s/success' % tmp_full_backup_dir, 'w').close()
        log('*** success: %s : %sG' % (tmp_full_path_backup_file, tmp_backup_file_size))

    # Remove oldest if more than tmp_vm_max_backups
    dir_to_remove = get_dir_to_remove(tmp_vm_backup_dir, tmp_vm_max_backups)
    while (dir_to_remove):
        log ('Deleting oldest backup %s/%s ' % (tmp_vm_backup_dir, dir_to_remove))
        # remove dir - if throw exception then stop processing
        shutil.rmtree(tmp_vm_backup_dir + '/' + dir_to_remove)
        dir_to_remove = get_dir_to_remove(tmp_vm_backup_dir, tmp_vm_max_backups)

def pre_cleanup(tmp_vm_backup_dir, tmp_vm_max_backups):
  log('success identifying directory : %s ' % tmp_vm_backup_dir)
  # Remove oldest if more than tmp_vm_max_backups -1
  pre_vm_max_backups = tmp_vm_max_backups - 1
  log ("pre_VM_max_backups: %s " % pre_vm_max_backups)
  if pre_vm_max_backups < 1:
     log ('No pre_cleanup needed for %s ' % tmp_vm_backup_dir)
  else:
     dir_to_remove = get_dir_to_remove(tmp_vm_backup_dir, tmp_vm_max_backups)
     while (dir_to_remove):
        log ('Deleting oldest backup %s/%s ' % (tmp_vm_backup_dir, dir_to_remove))
        # remove dir - if throw exception then stop processing
        shutil.rmtree(tmp_vm_backup_dir + '/' + dir_to_remove)
        dir_to_remove = get_dir_to_remove(tmp_vm_backup_dir, tmp_vm_max_backups)

# cleanup old unsuccessful backup and create new full_backup_dir
def process_backup_dir(tmp_vm_backup_dir):

    if (not os.path.exists(tmp_vm_backup_dir)):
        # Create new dir - if throw exception then stop processing
        os.mkdir(tmp_vm_backup_dir)

    # if last backup was not successful, then delete it
    log ('Check for last **unsuccessful** backup: %s' % tmp_vm_backup_dir)
    dir_not_success = get_last_backup_dir_that_failed(tmp_vm_backup_dir)
    if (dir_not_success):
        log ('Delete last **unsuccessful** backup %s/%s ' % (tmp_vm_backup_dir, dir_not_success))
        # remove last unseccessful backup  - if throw exception then stop processing
        shutil.rmtree(tmp_vm_backup_dir + '/' + dir_not_success)

    # create new backup dir
    return create_full_backup_dir(tmp_vm_backup_dir)

# Setup full backup dir structure
def create_full_backup_dir(vm_base_path):
    # Check that directory exists
    if not os.path.exists(vm_base_path):
        # Create new dir - if throw exception then stop processing
        os.mkdir(vm_base_path)

    date = datetime.datetime.today()
    tmp_backup_dir = BACKUP_DIR_PATTERN \
    % (vm_base_path, date.year, date.month, date.day, date.hour, date.minute, date.second)
    log('new backup_dir: %s' % tmp_backup_dir)

    if not os.path.exists(tmp_backup_dir):
        # Create new dir - if throw exception then stop processing
        os.mkdir(tmp_backup_dir)

    return tmp_backup_dir

# Setup meta dir structure
def get_meta_path(base_path):
    # Check that directory exists
    if not os.path.exists(base_path):
        # Create new dir
        try:
            os.mkdir(base_path)
        except OSError as error:
            log('ERROR creating directory %s : %s' % (base_path, error))
            return False

    date = datetime.datetime.today()
    backup_path = '%s/pool_db_%04d%02d%02d-%02d%02d%02d.dump' \
    % (base_path, date.year, date.month, date.day, date.hour, date.minute, date.second)

    return backup_path

def get_dir_to_remove(path, numbackups):
    # Find oldest backup and select for deletion
    dirs = os.listdir(path)
    dirs.sort()
    if (len(dirs) > numbackups and len(dirs) > 1):
        return dirs[0]
    else:
        return False

def get_last_backup_dir_that_failed(path):
    # if the last backup dir was not success, then return that backup dir
    dirs = os.listdir(path)
    if (len(dirs) <= 1):
        return False
    dirs.sort()
    # note: dirs[-1] is the last entry
    if (not os.path.exists(path + '/' + dirs[-1] + '/success')) and \
        (not os.path.exists(path + '/' + dirs[-1] + '/success_restore')) and \
        (not os.path.exists(path + '/' + dirs[-1] + '/success_compress' )) and \
        (not os.path.exists(path + '/' + dirs[-1] + '/success_compressing' )):
        return dirs[-1]
    else:
        return False

def check_all_backups_success(path):
    # expect at least one backup dir, and all should be successful
    dirs = os.listdir(path)
    if (len(dirs) == 0):
        return False
    for dir in dirs:
        if (not os.path.exists(path + '/' + dir + '/success' )) and \
            (not os.path.exists(path + '/' + dir + '/success_restore' )) and \
            (not os.path.exists(path + '/' + dir + '/success_compress' )) and \
            (not os.path.exists(path + '/' + dir + '/success_compressing' )):
            log("WARNING: directory not successful - %s" % dir)
            return False
    return True

def backup_pool_metadata(svr_name):

    # xe-backup-metadata can only run on master
    if not is_xe_master():
        log('** ignore: NOT master')
        return True

    metadata_base = os.path.join(config['backup_dir'], 'METADATA_' + svr_name)
    metadata_file = get_meta_path(metadata_base)
    if not metadata_file:
        return False

    cmd = "%s/xe pool-dump-database file-name='%s'" % (xe_path, metadata_file)
    log(cmd)
    if run_log_out_wait_rc(cmd) != 0:
        log('ERROR failed to backup pool metadata')
        return False

    return True

# some run notes with xe return code and output examples
#  xe vm-lisX -> error .returncode=1 w/ error msg
#  xe vm-list name-label=BAD-vm-name -> success .returncode=0 with no output
#  xe pool-dump-database file-name=<dup-file-already-exists>
#     -> error .returncode=1 w/ error msg
def run_log_out_wait_rc(cmd, log_w_timestamp=True):
    child = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, shell=True, universal_newlines=True)
    line = child.stdout.readline()
    while line:
        log(line.rstrip("\n"), log_w_timestamp)
        line = child.stdout.readline()
    return child.wait()

def run_log_out_wait_rc_ret_output(cmd, log_w_timestamp=True):
    child = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, shell=True, universal_newlines=True)
    line = child.stdout.readline()
    output = []
    while line:
        linestring = line.strip()
        if linestring != '':
            log(line.rstrip("\n"), log_w_timestamp)
            output.append(linestring)
        line = child.stdout.readline()
    child.wait()
    return output

def run_get_lastline(cmd):
    # exec cmd - expect 1 line output from cmd
    # return last line
    f = os.popen(cmd)
    resp = ''
    for line in f.readlines():
        resp = line.rstrip("\n")
    f.close()
    return resp

def get_os_version(uuid):
    cmd = "%s/xe vm-list uuid='%s' params=os-version | /bin/grep 'os-version' | /bin/awk -F'name: ' '{print $2}' | /bin/awk -F'|' '{print $1}' | /bin/awk -F';' '{print $1}'" % (xe_path, uuid)
    return run_get_lastline(cmd)

def df_snapshots(log_msg):
    log(log_msg)
    f = os.popen('df -Th %s' % config['backup_dir'])
    for line in f.readlines():
        line = line.rstrip("\n")
        log(line)
    f.close()

############################# mail

def config_value(key, default=''):
    # scalar config value; a key given twice in the file ends up as a list, the last one wins
    value = config.get(key, '')
    if isinstance(value, list):
        value = value[-1]
    return str(value).strip() or default

def mail_setting(key, legacy_default=''):
    return config_value(key, legacy_default)

def mail_wanted(overall):
    to = mail_setting('mail_to', MAIL_TO_ADDR)
    if not to:
        return False
    mode = (mail_setting('mail_mode') or DEFAULT_MAIL_MODE).lower()
    if mode == 'never':
        return False
    if mode == 'problems':
        return overall != 'success'
    return True

def send_email(to, subject, body_fname):

    smtp_send_retries = 3
    smtp_send_attempt = 0

    try:
        with open('%s' % body_fname, 'r') as f:
            body = f.read()
    except OSError:
        body = message

    msg = MIMEText(body)
    msg['subject'] = subject
    mail_from = mail_setting('mail_from', MAIL_FROM_ADDR)
    server = mail_setting('mail_smtp_server', MAIL_SMTP_SERVER)
    port = int(mail_setting('mail_smtp_port') or DEFAULT_MAIL_SMTP_PORT)
    username = secrets.get('mailuser', '')
    password = secrets.get('mailpass', '')
    msg['From'] = mail_from
    msg['To'] = to

    while smtp_send_attempt < smtp_send_retries:
        smtp_send_attempt += 1
        try:
            # note if using an ipaddress for the server,
            # then may require smtplib.SMTP(server, local_hostname="localhost")
            if port == 465:
                s = smtplib.SMTP_SSL(server, port, timeout=60)
            else:
                s = smtplib.SMTP(server, port, timeout=60)
                s.ehlo()
                if port != 25 or s.has_extn('STARTTLS'):
                    s.starttls()
                    s.ehlo()
            if username:
                s.login(username, password)
            s.sendmail(mail_from, to.split(','), msg.as_string())
            s.quit()
            log('mail sent to %s via %s:%s' % (to, server, port))
            break
        except socket.error as e:
            print("Exception: socket.error -  %s" % e, flush=True)
            time.sleep(5)
        except smtplib.SMTPException as e:
            print("Exception: SMTPException - %s" % e, flush=True)
            time.sleep(5)
    else:
        log('WARNING mail could not be sent after %s attempts' % smtp_send_retries)

############################# secrets

def load_secrets(path):
    # key=value lines, chmod 600; keys used here: mailuser, mailpass, api_token
    # (lukspass is read by runBackup.sh, not by this script)
    loaded = {}
    if not path or not os.path.exists(path):
        return loaded
    try:
        mode = os.stat(path).st_mode & 0o777
        if mode & 0o077:
            print('WARNING %s is readable by others (mode %o), expected 600' % (path, mode), flush=True)
        with open(path) as f:
            for line in f:
                line = line.rstrip('\n')
                if not line or line.startswith('#') or '=' not in line:
                    continue
                k, v = line.split('=', 1)
                loaded[k.strip()] = v.strip()
    except OSError as e:
        print('WARNING cannot read secrets file %s: %s' % (path, e), flush=True)
    return loaded

############################# config

def is_xe_master():
    # test to see if we are running on xe master

    cmd = '%s/xe pool-list params=master --minimal' % xe_path
    master_uuid = run_get_lastline(cmd)

    hostname = os.uname()[1]
    cmd = '%s/xe host-list name-label=%s --minimal' % (xe_path, hostname)
    host_uuid = run_get_lastline(cmd)
    if host_uuid == '':
        # the host name-label may differ from the hostname (XCP-ng sets it independently)
        cmd = '%s/xe host-list hostname=%s --minimal' % (xe_path, hostname)
        host_uuid = run_get_lastline(cmd)

    if host_uuid == master_uuid:
        return True

    return False

def is_config_valid():

    if not isInt(config['pool_db_backup']):
        print('ERROR: config pool_db_backup non-numeric -> %s' % config['pool_db_backup'])
        return False

    if int(config['pool_db_backup']) != 0 and int(config['pool_db_backup']) != 1:
        print('ERROR: config pool_db_backup out of range -> %s' % config['pool_db_backup'])
        return False

    if not isInt(config['max_backups']):
        print('ERROR: config max_backups non-numeric -> %s' % config['max_backups'])
        return False

    if int(config['max_backups']) < 1:
        print('ERROR: config max_backups out of range -> %s' % config['max_backups'])
        return False

    if config['vdi_export_format'] != 'raw' and config['vdi_export_format'] != 'vhd':
        print('ERROR: config vdi_export_format invalid -> %s' % config['vdi_export_format'])
        return False

    if not os.path.exists(config['backup_dir']):
        print('ERROR: config backup_dir does not exist -> %s' % config['backup_dir'])
        return False

    if compress not in ('none', 'gzip', 'zstd'):
        print('ERROR: compress must be none, gzip or zstd -> %s' % compress)
        return False

    mode = (mail_setting('mail_mode') or DEFAULT_MAIL_MODE).lower()
    if mode not in ('always', 'problems', 'never'):
        print('ERROR: mail_mode must be always, problems or never -> %s' % mode)
        return False

    tmp_return = True
    for vm_parm in config['vdi-export']:
        if not is_vm_backups_valid(vm_parm):
            print('ERROR: vm_max_backup is invalid - %s' % vm_parm)
            tmp_return = False

    for vm_parm in config['vm-export']:
        if not is_vm_backups_valid(vm_parm):
            print('ERROR: vm_max_backup is invalid - %s' % vm_parm)
            tmp_return = False

    return tmp_return

def config_load(path):
    return_value = True
    with open(path, 'r') as config_file:
        for line in config_file:
            if (not line.startswith('#') and len(line.strip()) > 0):
                (key,value) = line.strip().split('=', 1)
                key = key.strip()
                value = value.strip()

                # check for valid keys
                if not key in expected_keys:
                    if ignore_extra_keys:
                        log('ignoring config key: %s' % key)
                    else:
                        print('***ERROR unexpected config key: %s' % key)
                        return_value = False

                if key == 'exclude':
                    save_to_config_exclude( key, value)
                elif key in ['vm-export','vdi-export']:
                    save_to_config_export( key, value)
                else:
                    # all other key's
                    save_to_config_values( key, value)

    return return_value

def save_to_config_exclude( key, vm_name):
    # save key/value in config[]
    # expected-key: exclude
    # expected-value: vmname (with or w/o regex)
    global warning_match
    global error_regex
    found_match = False
    # Fail fast if exclude param given but empty to prevent from exluding all VMs
    if vm_name == "":
        return
    if not isNormalVmName(vm_name) and not isRegExValid( vm_name):
        log("***ERROR - invalid regex: %s=%s" % (key, vm_name))
        error_regex = True
        return
    for vm in all_vms:

        if ((isNormalVmName(vm_name) and vm_name == vm) or
            (not isNormalVmName(vm_name) and re.match(vm_name, vm))):
            found_match = True
            config[key].append(vm)

    if not found_match:
        log("***WARNING - vm not found: %s=%s" % (key, vm_name))
        warning_match = True
    else:
        for vm in config[key]:
            try:
               all_vms.remove(vm)
            except ValueError:
               pass

def save_to_config_export( key, value):
    # save key/value in config[]
    # expected-key: vm-export or vdi-export
    # expected-value: vmname (with or w/o regex) or vmname:#
    global warning_match
    global error_regex
    found_match = False

    # Fail fast if all VMs excluded or if no VMs exist in the pool
    if all_vms == []:
        return

    # Fail fast if vdi-export given but empty to prevent from matching all VMs first-come-first-served style
    # NOTE: This checks for the vdi-export key only so leaving vm-export empty will still default to all VMs
    if key == "vdi-export" and value == "":
        return

    # Evaluate key/value pairs if we get this far
    values = value.split(':')
    vm_name_part = values[0]
    vm_backups_part = ''
    if len(values) > 1:
        vm_backups_part = values[1]
    if not isNormalVmName(vm_name_part) and not isRegExValid( vm_name_part ):
        log("***ERROR - invalid regex: %s=%s" % (key, value))
        error_regex = True
        return
    for vm in all_vms:
        if ((isNormalVmName(vm_name_part) and vm_name_part == vm) or
            (not isNormalVmName(vm_name_part) and re.match(vm_name_part, vm))):
            if vm_backups_part == '':
                new_value = vm
            else:
                new_value = "%s:%s" % (vm, vm_backups_part)
            found_match = True
            # Check if vdi-export already has the vm mentioned and, if so, do not add this vm to vm-export
            if key == "vm-export" and vm in config['vdi-export']:
                continue
            else:
                config[key].append(new_value)
    if not found_match:
        log("***WARNING - vm not found: %s=%s" % (key, value))
        warning_match = True

def isNormalVmName( name ):
    if re.match(r'^[\w\s\-\_]+$', name) is not None:
        # normal vm name such as 'PRD-test123'
        return True
    else:
        # verses vm name using regex such as '^PRD-test[1-2]$'
        return False

def isRegExValid( text ):
    try:
        re.compile(text)
        return True
    except re.error:
        return False

def save_to_config_values( key, value):
    # save key/value in config[]
    # expected-key: any key except vm-export or vdi-export or exclude
    # expected-value: any value
    if key in config.keys():
        if type(config[key]) is list:
            config[key].append(value)
        else:
            config[key] = [config[key], value]
    else:
        config[key] = value

def verify_config_vms_exist():

    all_vms_exist = True
    # verify all VMs in vm/vdi-export exist
    vm_export_errors = verify_export_vms_exist()
    if vm_export_errors != '':
        all_vms_exist = False
        log('ERROR - vm(s) List does not exist: %s' % vm_export_errors)

    # verify all VMs in exclude exist
    vm_exclude_errors = verify_exclude_vms_exist()
    if vm_exclude_errors != '':
        log('***WARNING - vm(s) Exclude does not exist: %s' % vm_exclude_errors)

    return all_vms_exist

def verify_export_vms_exist():

    vm_error = ''
    for vm_parm in config['vdi-export']:
        # verify vm exists
        vm_name_part = get_vm_name(vm_parm)
        if not verify_vm_exist(vm_name_part):
            vm_error += vm_name_part + ' '

    for vm_parm in config['vm-export']:
        # verify vm exists
        vm_name_part = get_vm_name(vm_parm)
        if not verify_vm_exist(vm_name_part):
            vm_error += vm_name_part + ' '

    return vm_error

def verify_exclude_vms_exist():

    vm_error = ''
    for vm_parm in config['exclude']:
        # verify vm exists
        vm_name_part = get_vm_name(vm_parm)
        if not verify_vm_exist(vm_name_part):
            vm_error += vm_name_part + ' '

    return vm_error

def verify_vm_exist(vm_name):

    vm = session.xenapi.VM.get_by_name_label(vm_name)
    if (len(vm) == 0):
        return False
    else:
        return True

def get_all_vms():
    cmd = "%s/xe vm-list is-control-domain=false is-a-snapshot=false params=name-label --minimal" % xe_path
    vms = run_get_lastline(cmd)
    return vms.split(',')

def show_vms_not_in_backup():
    # show all vm's not in backup scope
    all_vms = get_all_vms()
    for vm_parm in config['vdi-export']:
        # remove from all_vms
        vm_name_part = get_vm_name(vm_parm)
        if vm_name_part in all_vms:
            all_vms.remove(vm_name_part)

    for vm_parm in config['vm-export']:
        # remove from all_vms
        vm_name_part = get_vm_name(vm_parm)
        if vm_name_part in all_vms:
            all_vms.remove(vm_name_part)

    vms_not_in_backup = ''
    for vm_name in all_vms:
        vms_not_in_backup += vm_name + ' '
    log('VMs-not-in-backup: %s' % vms_not_in_backup)

def cleanup_vmexport_vdiexport_dups():
    # if any vdi-export's exist in vm-export's then remove from vm-export
    for vdi_parm in config['vdi-export']:
        # vdi_parm has form PRD-name or PRD-name:5
        tmp_vdi_parm = get_vm_name(vdi_parm)
        for vm_parm in list(config['vm-export']):
            tmp_vm_parm = get_vm_name(vm_parm)
            if tmp_vm_parm == tmp_vdi_parm:
                log('***WARNING vdi-export duplicate - removing vm-export=%s' % vm_parm)
                config['vm-export'].remove(vm_parm)
    # remove duplicates
    config['vdi-export']=RemoveDup(config['vdi-export'])
    config['vm-export']=RemoveDup(config['vm-export'])

def RemoveDup(duplicate):
  final_list=[]
  for val in duplicate:

    # check if version exists and if so, take account of extra versions
    # as well as if a numbered wildcarded version already exists!
    versioned=0
    accounted=0
    # version flag here for debugging and tracking purposes, only
    if (val.find(':')!=-1):
       # found version in new VM entry and need to expand
       (valroot,numb) = val.split(':')
       versioned=1
    else:
       versioned=0
       # set root to be the same
       valroot=val

    # Need to replace old with new if found
    # Redo list and replace with new value
    alen=len(final_list)
    i=0
    while i < alen:
       if (final_list[i].find(':')!=-1):
         (finroot,fnumb)= final_list[i].split(':')
       else:
         finroot=final_list[i]
       if (valroot == finroot):
          #root matches, hence replace
          final_list[i]=val

          # check again if excluded
          j=0
          elen=len(config['exclude'])
          while j < elen:
             eroot=config['exclude'][j]
             if (valroot == eroot):
                # remove from list
                log ('***WARNING - forcing exclude of: %s ' % final_list[i])
                accounted=1
                final_list.remove(final_list[i])
                break
             else:
                j=j+1

          # VM has been accounted for
          accounted=1
          break
       else:
          i=i+1

    # need to check plain case if not accounted for yet
    # However, check again if excluded and if so, do not add to list
    j=0
    elen=len(config['exclude'])
    while j < elen:
       eroot=config['exclude'][j]
       if (valroot == eroot):
          # prevent from being added back onto the list
          log ('***WARNING - forcing exclude of: %s ' % val)
          accounted=1
          break
       else:
          j=j+1

    if (accounted == 0):
      if val not in final_list:
        final_list.append(val)
      else:
        # it should now never actually get here!
        print('SHOULD NEVER GET HERE  ----- found duplicate: %s' % val)

  return final_list

def config_load_defaults():
    # init config param not already loaded then load with default values
    if not 'pool_db_backup' in config.keys():
        config['pool_db_backup'] = str(DEFAULT_POOL_DB_BACKUP)
    if not 'max_backups' in config.keys():
        config['max_backups'] = str(DEFAULT_MAX_BACKUPS)
    if not 'vdi_export_format' in config.keys():
        config['vdi_export_format'] = str(DEFAULT_VDI_EXPORT_FORMAT)
    if not 'backup_dir' in config.keys():
        config['backup_dir'] = str(DEFAULT_BACKUP_DIR)
    if not 'status_log' in config.keys():
        config['status_log'] = str(DEFAULT_STATUS_LOG)

def config_print():
    log('VmBackup.py %s running with these settings:' % VERSION)
    log('  backup_dir        = %s' % config['backup_dir'])
    log('  status_log        = %s' % config['status_log'])
    log('  compress          = %s' % compress)
    log('  max_backups       = %s' % config['max_backups'])
    log('  vdi_export_format = %s' % config['vdi_export_format'])
    log('  pool_db_backup    = %s' % config['pool_db_backup'])
    log('  secrets_file      = %s (%s)' % (secrets_file, 'loaded' if secrets else 'not found'))
    log('  mail_to           = %s (%s)' % (mail_setting('mail_to', MAIL_TO_ADDR) or '-', mail_setting('mail_mode') or DEFAULT_MAIL_MODE))
    log('  api_report        = %s (%s)' % ('on' if api_report_wanted() else 'off', config_value('api_url') or DEFAULT_API_URL))

    log('  exclude (cnt)= %s' % len(config['exclude']))
    log('  exclude: %s' % ', '.join(sorted(config['exclude'])))

    log('  vdi-export (cnt)= %s' % len(config['vdi-export']))
    log('  vdi-export: %s' % ', '.join(sorted(config['vdi-export'])))

    log('  vm-export (cnt)= %s' % len(config['vm-export']))
    log('  vm-export: %s' % ', '.join(sorted(config['vm-export'])))

############################# status log

def status_log_write(rec):
    with open(config['status_log'], 'a') as f:
        f.write(rec)

def status_log_begin(server):
    status_log_write('%s,vmbackup.py,%s,begin\n' % (fmtDateTime(), server))

def status_log_end(server, status):
    status_log_write('%s,vmbackup.py,%s,end,%s\n' % (fmtDateTime(), server, status))

def status_log_vm_export_begin(server, status):
    status_log_write('%s,vm-export,%s,begin,%s\n' % (fmtDateTime(), server, status))

def status_log_vm_export_end(server, status):
    status_log_write('%s,vm-export,%s,end,%s\n' % (fmtDateTime(), server, status))

def status_log_vdi_export_begin(server, status):
    status_log_write('%s,vdi-export,%s,begin,%s\n' % (fmtDateTime(), server, status))

def status_log_vdi_export_end(server, status):
    status_log_write('%s,vdi-export,%s,end,%s\n' % (fmtDateTime(), server, status))

def fmtDateTime():
    date = datetime.datetime.today()
    return '%02d/%02d/%02d %02d:%02d:%02d' \
        % (date.year, date.month, date.day, date.hour, date.minute, date.second)

def log(mes, log_w_timestamp=True):
    # note - send_email uses message
    global message

    date = datetime.datetime.today()
    if log_w_timestamp:
        text = '%02d-%02d-%02d-(%02d:%02d:%02d) - %s\n' \
            % (date.year, date.month, date.day, date.hour, date.minute, date.second, mes)
    else:
        text = '%s\n' % mes
    message += text

    print(text.rstrip("\n"), flush=True)

def run(cmd, do_log=True):
    proc = subprocess.Popen(cmd, stdout=PIPE, stderr=STDOUT, shell=True, universal_newlines=True)
    out = proc.communicate()[0]
    res = proc.returncode
    if (res):
      if (do_log):
          log('ERROR for cmd %s' % cmd)
          log(out)
      return False

    return True

############################# usage

def usage():
    print('Usage-basic:')
    print(sys.argv[0], ' <password|password-file|local> <config-file|vm-selector> [preview] [other optional params]')
    print()
    print('see also: VmBackup.py help    - for additional parameter usage')
    print('      or: VmBackup.py config  - for config-file parameter usage')
    print('      or: VmBackup.py example - for some simple example usage')
    print()

def usage_help():
    print('Usage-help:')
    print(sys.argv[0], ' <password|password-file|local> <config-file|vm-selector> [preview] [other optional params]')
    print()
    print('required params:')
    print('  <password|password-file|local> - xenserver root password, an obscured password stored in password-file,')
    print('      or the word "local" to use the local XenAPI unix socket (no password, run as root on the host)')
    print('  <config-file|vm-selector> - several options:')
    print('    config-file - a common choice for production crontab execution')
    print('    vm-selector - a single vm name or a vm reqular expression that defaults to vm-export')
    print('      note with vm-selector then config defaults are set from VmBackup.py default constantants')
    print('    vm-export=vm-selector  - explicit vm-export')
    print('    vdi-export=vm-selector - explicit vdi-export')
    print()
    print('optional params:')
    print('  [preview] - preview/validate VmBackup config parameters and xenserver password')
    print('  [compress=none|gzip|zstd] - vm-export compression (default: none; true=gzip, false=none;')
    print('      zstd needs XCP-ng 8.1+). Can also be set in the config file as compress=')
    print('  [ignore_extra_keys=True|False] - some config files may have extra params (default: False)')
    print('  [pre_clean=True|False] - delete older backup(s) before performing new backup (default: False)')
    print('  [secrets_file=PATH] - key=value file with mailuser, mailpass, api_token (default: %s)' % DEFAULT_SECRETS_FILE)
    print()
    print('exit codes: 0 success, 1 warnings, 2 errors (or fatal configuration problem)')
    print()
    print('alternate form - create-password-file:')
    print(sys.argv[0], ' <password> create-password-file=filename')
    print()
    print('  create-password-file=filename - create an obscured password file with the specified password')
    print('  note - password filename is relative to current path or absolute path.')
    print()

def usage_config_file():
    print('Usage-config-file:')
    print()
    print('  # Example config file for VmBackup.py')
    print()
    print('  #### high level VmBackup settings ################')
    print('  #### note - if any of these are not specified ####')
    print('  ####   then VmBackup uses default constants   ####')
    print()
    print('  # Take Xen Pool DB backup: 0=No, 1=Yes (script default to 0=No)')
    print('  pool_db_backup=0')
    print()
    print('  # How many backups to keep for each vm (script default to 4)')
    print('  max_backups=3')
    print()
    print('  #Backup Directory path (script default /snapshots/BACKUPS)')
    print('  backup_dir=/path/to/backupspace')
    print()
    print('  # vm-export compression: none, gzip or zstd (zstd needs XCP-ng 8.1+)')
    print('  compress=zstd')
    print()
    print('  # applicable if vdi-export is used')
    print('  # vdi_export_format either raw or vhd (script default to raw)')
    print('  vdi_export_format=raw')
    print()
    print('  # mail report (credentials in the secrets file as mailuser= / mailpass=)')
    print('  mail_to=backup@example.com')
    print('  mail_from=host@example.com')
    print('  mail_smtp_server=mail.example.com')
    print('  mail_smtp_port=587')
    print('  mail_mode=always      # always | problems | never')
    print()
    print('  # JSON report to the itsdave backup API (token in the secrets file as api_token=)')
    print('  api_url=https://backupapi.itsdave.de/api/v1')
    print('  api_hostname=host.example.com   # default: this hosts FQDN')
    print('  api_report=true')
    print()
    print('  #### specific VMs backup settings ####')
    print()
    print('  # vm-export VM name-label of vm to backup. One per line - notice :max_backups override.')
    print('  vm-export=my-vm-name')
    print('  vm-export=my-second-vm')
    print('  vm-export=my-third-vm:3')
    print()
    print('  # special vdi-export - only backs up first disk. See README Documenation!')
    print('  vdi-export=my-vm-name')
    print()
    print('  # vm-export using VM regular expression - notice DEV.* has :max_backups overide')
    print('  vm-export=PROD.*')
    print('  vm-export=DEV.*:2')
    print()
    print('  # exclude specific VMs')
    print('  exclude=PROD-WinDomainController')
    print('  exclude=DEV-DestructiveTest')
    print()
    print('  # disks whose VDI name-label starts with [NOBAK] are never exported')
    print()

def usage_examples():
    print('Usage-examples:')
    print()
    print('  # config file, local XenAPI socket (run as root on the host)')
    print('  ./VmBackup.py local weekend.cfg compress=zstd')
    print()
    print('  # single VM name, which is case sensitive')
    print('  ./VmBackup.py password DEV-mySql')
    print()
    print('  # single VM name using vdi-export instead of vm-export')
    print('  ./VmBackup.py password vdi-export=DEV-mySql')
    print()
    print('  # single VM name with spaces in name')
    print('  ./VmBackup.py password "DEV mySql"')
    print()
    print('  # VM regular expression - which may be more than one VM')
    print('  ./VmBackup.py password DEV-my.*')
    print()
    print('  # all VMs in pool')
    print('  ./VmBackup.py password ".*"')
    print()
    print('Alternate form - create-password-file:')
    print('  # create password file from command line password')
    print('  ./VmBackup.py password create-password-file=/root/VmBackup.pass')
    print()
    print('  # use password file + config file')
    print('  ./VmBackup.py /root/VmBackup.pass monthly.cfg')
    print()

def normalize_compress(value):
    value = str(value).strip().lower()
    if value in ('true', 'gzip', 'gz'):
        return 'gzip'
    if value in ('false', 'none', 'no', 'off', ''):
        return 'none'
    return value

def open_session(password):
    # "local": unix socket of the local xapi, no password needed. Otherwise https to localhost
    # (ignore_ssl because the host certificate is self-signed) with fallback to the pool master.
    if password == 'local':
        s = XenAPI.xapi_local()
        s.xenapi.login_with_password('root', '')
        return s
    try:
        s = XenAPI.Session('https://localhost/', ignore_ssl=True)
        s.xenapi.login_with_password('root', password)
        s.xenapi.host.get_all()
        return s
    except XenAPI.Failure as e:
        print(e)
        if e.details[0] == 'HOST_IS_SLAVE':
            s = XenAPI.Session('https://' + e.details[1], ignore_ssl=True)
            s.xenapi.login_with_password('root', password)
            s.xenapi.host.get_all()
            return s
        print('ERROR - XenAPI authentication error')
        sys.exit(2)

if __name__ == '__main__':
    if 'help' in sys.argv or 'config' in sys.argv or 'example' in sys.argv:
        if 'help' in sys.argv: usage_help()
        if 'config' in sys.argv: usage_config_file()
        if 'example' in sys.argv: usage_examples()
        sys.exit(1)
    if len(sys.argv) < 3:
        usage()
        sys.exit(1)
    password = sys.argv[1]
    cfg_file = sys.argv[2]
    # obscure password support
    if password != 'local' and (os.path.exists(password)):
        with open(password, 'r') as f:
            password = base64.b64decode(f.read()).decode('utf-8')
    if cfg_file.lower().startswith('create-password-file'):
        array = sys.argv[2].strip().split('=')
        with open(array[1], 'w') as f:
            f.write(base64.b64encode(password.encode('utf-8')).decode('ascii'))
        os.chmod(array[1], 0o600)
        print('password file saved to: %s' % array[1])
        sys.exit(0)

    # load optional params
    preview = False                 # default
    compress = None                 # default: from config file, else DEFAULT_COMPRESS
    ignore_extra_keys = False       # default
    pre_clean = False               # default
    secrets_file = DEFAULT_SECRETS_FILE

    # loop through remaining optional args
    arg_range = range(3,len(sys.argv))
    for arg_ix in arg_range:
        array = sys.argv[arg_ix].strip().split('=', 1)
        if array[0].lower() == 'preview':
            preview = True
        elif array[0].lower() == 'compress':
            compress = normalize_compress(array[1])
        elif array[0].lower() == 'ignore_extra_keys':
            ignore_extra_keys = (array[1].lower() == 'true')
        elif array[0].lower() == 'pre_clean':
            pre_clean = (array[1].lower() == 'true')
        elif array[0].lower() == 'secrets_file':
            secrets_file = array[1]
        else:
            print('ERROR invalid parm: %s' % sys.argv[arg_ix])
            usage()
            sys.exit(1)

    secrets = load_secrets(secrets_file)

    # init vm-export/vdi-export/exclude in config list
    config['vm-export'] = []
    config['vdi-export'] = []
    config['exclude'] = []
    warning_match = False
    error_regex = False

    all_vms = get_all_vms()

    # process config file
    if (os.path.exists(cfg_file)):
        # config file exists
        config_specified = 1
        if config_load(cfg_file):
            cleanup_vmexport_vdiexport_dups()
        else:
            print('ERROR in config_load, consider ignore_extra_keys=true')
            sys.exit(2)
    else:
        # no config file exists - so cfg_file is actual vm_name/prefix
        config_specified = 0
        cmd_option = 'vm-export' # default
        cmd_vm_name = cfg_file   # in this case a vm name pattern
        if cmd_vm_name.count('=') == 1:
            (cmd_option,cmd_vm_name) = cmd_vm_name.strip().split('=')
        if cmd_option != 'vm-export' and cmd_option != 'vdi-export':
            print('ERROR invalid config/vm_name: %s' % cfg_file)
            usage()
            sys.exit(1)
        save_to_config_export( cmd_option, cmd_vm_name)

    config_load_defaults()  # set defaults that are not already loaded
    if compress is None:
        compress = normalize_compress(config_value('compress') or DEFAULT_COMPRESS)
    log('VmBackup config loaded from: %s' % cfg_file)
    config_print()     # show fully loaded config

    if not is_config_valid():
        log('ERROR in configuration settings...')
        sys.exit(2)
    if len(config['vm-export']) == 0 and len(config['vdi-export']) == 0 :
        log('ERROR no VMs loaded')
        sys.exit(2)

    # acquire a xapi session by logging in
    session = open_session(password)

    if preview:
    # check for duplicate names
       log('Checking all VMs for duplicate names ...')
       for vm in all_vms:
          vmref = [x for x in session.xenapi.VM.get_by_name_label(vm) if not session.xenapi.VM.get_is_a_snapshot(x)]
          if (len(vmref) > 1):
             log ("*** ERROR: duplicate VM name found: %s | %s" % (vm, vmref))

    if not verify_config_vms_exist():
        # error message(s) printed in verify_config_vms_exist
        sys.exit(2)

    if preview:
        warning = ''
        if warning_match:
            warning = ' - WARNINGS found (see above)'
        if error_regex:
            log('ERROR regex errors found (see above) %s' % warning)
            sys.exit(2)
        log('SUCCESS preview of parameters %s' % warning)
        sys.exit(1 if warning_match else 0)

    warning = ''
    if warning_match:
        warning = ' - WARNINGS found (see above)'
    log('SUCCESS check of parameters %s' % warning)
    if error_regex:
        log('ERROR regex errors found (see above)')
        sys.exit(2)

    rc = 2
    try:
        rc = main(session)

    except Exception as e:
        print(e)
        log('***ERROR EXCEPTION - %s' % sys.exc_info()[0])
        log('***ERROR NOTE: see VmBackup output for details')
        raise
    finally:
        try:
            session.xenapi.session.logout()
        except Exception:
            pass
    sys.exit(rc)
