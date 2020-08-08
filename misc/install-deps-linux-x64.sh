#!/bin/bash

# Installs the following dependencies to ~/.local:
#  - tlc2 model checker
#  - stack build system
# NOTE: this script is specialized to Linux x86_64 environments.

set -e # exit if any command fails
set -x # print each command

INSTALL_DIR="$HOME/.local"
mkdir -p "$INSTALL_DIR"/{bin,lib}
export PATH=$INSTALL_DIR/bin:$PATH

# Download TLA+ command-line tools
if [[ ! -e "$INSTALL_DIR/lib/tla2tools.jar" ]]; then
    curl -Lf https://github.com/tlaplus/tlaplus/releases/download/v1.7.0/tla2tools.jar -o ~/.local/lib/tla2tools.jar
fi

# Create `tlc2` script
if [[ ! -x "$INSTALL_DIR/bin/tlc2" ]]; then
    # NOTE: environment variables (e.g. $INSTALL_DIR) _are_ expanded in heredocs.
    cat >"$INSTALL_DIR/bin/tlc2" <<EOF
#!/bin/bash
export CLASSPATH="$INSTALL_DIR/lib/tla2tools.jar"
exec java -XX:+UseParallelGC tlc2.TLC "\$@"
EOF
    chmod +x "$INSTALL_DIR/bin/tlc2"
fi

# Download and unpack the stack executable
# (NOTE: requires GNU Tar; does not work with BSD Tar)
if [[ ! -x "$INSTALL_DIR/bin/stack" ]]; then
    curl -Lf https://get.haskellstack.org/stable/linux-x86_64.tar.gz \
        | tar xz --wildcards --strip-components=1 -C "$INSTALL_DIR/bin" '*/stack'
fi
