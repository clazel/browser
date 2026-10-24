#!/bin/sh
# Installs a clazel release: run it from the unpacked tarball, as root for
# the default prefix.
#
#   sudo ./install.sh                 # into /usr/local
#   sudo PREFIX=/opt/clazel ./install.sh
#
# The binaries go to $PREFIX/lib/clazel/ (clazel finds clazel-renderer next
# to itself), with $PREFIX/bin/clazel linking to them. On Linux systems that
# restrict unprivileged user namespaces through AppArmor (Ubuntu 23.10 and
# later), it also installs a profile that lets clazel-renderer create the
# user namespace its sandbox needs (apparmor/allow-userns.sh says exactly
# what it grants). Without it the renderer refuses to start, by design.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
prefix=${PREFIX:-/usr/local}
lib=$prefix/lib/clazel

mkdir -p "$lib" "$prefix/bin"
install -m 0755 "$here/clazel" "$here/clazel-renderer" "$lib/"
ln -sf "$lib/clazel" "$prefix/bin/clazel"
echo "install: clazel and clazel-renderer in $lib, $prefix/bin/clazel links to them"

if [ "$(uname -s)" = Linux ]; then
    "$here/apparmor/allow-userns.sh" clazel-renderer "$lib/clazel-renderer"
fi
