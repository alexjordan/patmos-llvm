#!/bin/bash
#
# platin installation script
#

SRC_DIR=$(dirname "${0}")

function usage() {
    echo "usage: ${0} -i INSTALL_DIR [-d]" >&2
    echo >&2
    echo "Install the platin toolchain relative to the given prefix" >&2
    echo "Installed Files: " >&2
    echo "  <prefix>/bin/platin      ... Binary" >&2
    echo "  <prefix>/lib/platin/     ... Library Directory" >&2
    echo "  <prefix>/lib/platin/gems ... Ruby Libraries (if necessary)" >&2
    echo "OPTIONS" >&2
    echo "  -d     dry run" >&2
    echo "  -v     verbose" >&2
    exit 1

}

while getopts "hi:dvx" opt; do
  case $opt in
    h) usage; exit 0 ;;
    i) INSTALL_DIR="${OPTARG}" ;;
    d) DRYRUN=true; VERBOSE=true ;;
    v) VERBOSE=true ;;
    x) set -x ;;
    :)
      echo "Option -$OPTARG requires an argument." >&2
      usage >&2
      exit 1
      ;;
  esac
done

if [ -z "${INSTALL_DIR}" ] ; then
    usage
fi

BINARY="${INSTALL_DIR}/bin/platin"
LIB_DIR="${INSTALL_DIR}/lib/platin"
GEM_DIR="${LIB_DIR}/gems"

function info() {
    if [ ! -z "${VERBOSE}" ] ; then
	echo 'INFO' "${@}"
    else
	echo "${@}"
    fi
}

function install() {
    DST="${1}"
    SRC="${2}"
    info "Installing ${SRC} -> ${DST}"
    run mkdir -p "$(dirname "${DST}")"
    run cp "${SRC}" "${DST}"
}

function verbose() {
    if [ ! -z "${VERBOSE}" ] ; then
	echo "${@}"
    fi
}
function run() {
    CMD="${1}"
    shift
    verbose "${CMD}" "${@}"
    if [ -z "${DRYRUN}" ] ; then
	"${CMD}" "${@}"
    fi
}

function install_binary() {
    install "${BINARY}" "${SRC_DIR}/platin"
    if [ -z "${DRYRUN}" ] ; then
	cat <<EOF >"${BINARY}"
#!/bin/bash

# Installer
RELATIVE_LIBDIR="../lib/platin"

# Local Gems
if [ -z "\${GEM_PATH}" ] ; then
  export GEM_PATH="${GEM_DIR}"
else
  export GEM_PATH="${GEM_DIR}:\${GEM_PATH}"
fi
# Executable
EOF
	cat "${SRC_DIR}/platin"  >> "${BINARY}"
    fi
    run chmod uga+x "${BINARY}"
}

install_binary

for libfile in $(cd "${SRC_DIR}/lib" ; find "." -name '*.rb') ; do
    SRC="${SRC_DIR}/lib/${libfile}"
    DST="${INSTALL_DIR}/lib/platin/${libfile}"
    install "${DST}" "${SRC}"
done

function detect_gem_command {
    GEM19s="gem1.9.1 gem1.9 gem"
    for g19 in ${GEM19s} ; do
        if [ ! -z "`which ${g19}  2>/dev/null`" ] ; then
            GEM="$g19"
            return
        fi
    done
}

detect_gem_command
if [ ! -z "${GEM}" ] ; then
    if [ -z "${GEM_PATH}" ] ; then
	export GEM_PATH="${GEM_DIR}"
    else
	export GEM_PATH="${GEM_DIR}:${GEM_PATH}"
    fi
    for gemqname in rsec:0.4 ruby-graphviz:1.0.8 lpsolve:5.5.10.j ; do
	gemname=$(echo "${gemqname}" | cut -d':' -f1)
	gemversion=$(echo "${gemqname}" | cut -d':' -f2)
	verbose "INFO checking for gem ${gemqname}"
	if [ "$(${GEM} list ${gemname} --version ${gemversion} -i)" != "true" ] ; then
	    info "Installing gem ${gemname} --version ${gemversion} (missing)"
	    local_gemfile="${SRC_DIR}/ext/${gemname}-${gemversion}.gem"
	    if [ -z "${DRYRUN}" ] ; then
		if [ -e "${local_gemfile}" ] ; then
		    gem_args="${local_gemfile}"
		else
		    gem_args="${gemname} --version ${gemversion}"
		fi
		"${GEM}" install --install-dir "${GEM_DIR}" ${gem_args}  -q 2>&1 | sed 's/^/[GEM] /'
		if [ "${PIPESTATUS[0]}" -ne 0 ] ; then
		    echo "WARNING: failed to install gem ${gem_args}. platin will not work." >&2
		fi
	    fi
	fi
    done	
else
    echo "WARNING: did not find 'gem' command; skipping ruby library checks" >&2
fi