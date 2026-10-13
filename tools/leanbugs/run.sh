#!/bin/sh
# usage: run.sh <id> <toolchain> <source.lean> ; builds a scratch project, exports Repro, runs the kernels
export PATH=$HOME/.elan/bin:/opt/homebrew/opt/openjdk@21/bin:$PATH DOTNET_ROOT=/opt/homebrew/opt/dotnet/libexec
id=$1; tc=$2; src=$3; LB=$HOME/lean-ext/e85-work/lb; P=$LB/$id; X=$HOME/lean-ext/lean4export-${tc}
rm -rf $P; mkdir -p $P; cd $P
printf 'leanprover/lean4:v%s\n' $tc > lean-toolchain
printf 'name = "repro"\ndefaultTargets = ["Repro"]\n[[lean_lib]]\nname = "Repro"\n' > lakefile.toml
cp $src Repro.lean
lake build Repro > build.log 2>&1; brc=$?
echo "$id build rc=$brc $(grep -c 'error' build.log) error-lines"
grep -E "error|axioms|mutB|KIPData" build.log | head -4 | sed 's/^/    /' | cut -c1-140
[ -f .lake/build/lib/lean/Repro.olean ] || { echo "    no olean"; exit 0; }
(cd $X && LEAN_PATH="$(lake env printenv LEAN_PATH):$P/.lake/build/lib/lean" .lake/build/bin/lean4export Repro > $P/repro.ndjson 2> $P/export.err); echo "    export: $(wc -l < repro.ndjson) lines $(head -c 120 export.err)"
JAVA_OPTS="-Xss512m -Xmx4g" $HOME/tenet-jvm/bin/tenet-jvm --keep-going repro.ndjson > jvm.out 2>&1; echo "    tenet-jvm rc=$? : $(grep -E 'REJECTED|verified' jvm.out | head -2 | tr '\n' ' ' | cut -c1-200)"
$HOME/tenet/src/Tenet.Cli/bin/Release/net10.0/tenet check repro.ndjson > tenet.out 2>&1; echo "    tenet     rc=$? : $(grep -E 'OK:|failed|declined|FAIL' tenet.out | tail -1 | cut -c1-200)"
