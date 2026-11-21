set -eu

heresy=$(realpath "$1")
certificate=$(realpath "$2")
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

. "$3"
