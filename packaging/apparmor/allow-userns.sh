#!/bin/sh
# Lets the named programs create user namespaces on systems that restrict
# them through AppArmor (Ubuntu 23.10 and later), by installing and loading
# an AppArmor profile for exactly those programs.
#
# Usage (as root): allow-userns.sh NAME ATTACHMENT
#   NAME        the profile's name, also its file name in /etc/apparmor.d/
#   ATTACHMENT  the absolute path of the program, or an AppArmor glob of
#               several (e.g. /opt/x/{a,b})
#
# The Linux renderer sandbox (crates/clazel-renderer/src/sandbox.rs) enters
# new user, mount, PID, network and IPC namespaces before reading any input,
# and fails closed if it cannot. Ubuntu's sysctl
# kernel.apparmor_restrict_unprivileged_userns=1 refuses that to every
# program without a profile granting `userns`; browsers ship one such
# profile each, and this is ours. It grants `userns` and nothing else: the
# programs stay otherwise unconfined by AppArmor, and Landlock and seccomp
# still apply inside the renderer.
#
# Where the restriction is absent or off, nothing is installed.
set -eu

name=$1
attach=$2
knob=/proc/sys/kernel/apparmor_restrict_unprivileged_userns

if [ ! -r "$knob" ]; then
    echo "allow-userns: $knob does not exist; user namespaces are not restricted by AppArmor here"
    exit 0
fi
value=$(cat "$knob")
echo "allow-userns: kernel.apparmor_restrict_unprivileged_userns = $value"
if [ "$value" = 0 ]; then
    echo "allow-userns: not restricted; nothing to install"
    exit 0
fi
if ! command -v apparmor_parser >/dev/null 2>&1; then
    echo "allow-userns: user namespaces are restricted but apparmor_parser is missing" >&2
    exit 1
fi

profile=/etc/apparmor.d/$name
cat > "$profile" <<PROFILE
# Installed by clazel's packaging/apparmor/allow-userns.sh: lets $name
# create the user namespace its sandbox needs. Nothing else is granted.
abi <abi/4.0>,
include <tunables/global>

profile $name $attach flags=(unconfined) {
  userns,

  include if exists <local/$name>
}
PROFILE
apparmor_parser --replace "$profile"
echo "allow-userns: loaded $profile for $attach"
