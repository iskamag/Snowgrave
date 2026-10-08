#!/bin/sh
# Execute only the image produced by mezzano-materializer-image.lisp in an owned cache.
set -eu
: "${SNOWGRAVE_MEZZANO_CACHE:?Set the owned native materializer image cache}"
task_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
serial="$task_root/.build/mezzano-materializer-runtime-serial.log"
qemu_log="$task_root/.build/mezzano-materializer-runtime-qemu.log"
set +e
timeout --signal=TERM 75 qemu-system-x86_64 -enable-kvm -machine pc -m 3G -smp 2 \
  -drive "file=$SNOWGRAVE_MEZZANO_CACHE/materializer-image.image,format=raw,if=ide" \
  -snapshot -serial "file:$serial" -monitor none -display none -vga std \
  -net none -no-reboot > "$qemu_log" 2>&1
status=$?
set -e
case "$status" in 0|124) ;; *) exit "$status" ;; esac
if rg -q 'PANIC' "$serial"; then cat "$serial"; exit 1; fi
for marker in SNOWGRAVE-MATERIALIZER-NATIVE-PAYLOAD24 \
  SNOWGRAVE-MATERIALIZER-POSITIVE48 'SNOWGRAVE-MATERIALIZER-BYTES FIRST 0' \
  'SNOWGRAVE-MATERIALIZER-BYTES ROUND256 0' SNOWGRAVE-MATERIALIZER-NATIVE-PASSED 'Hello, world'; do
  rg -q -F "$marker" "$serial"
done
printf '%s\n' 'Snowgrave native typed record/array boundary fixture PASS.'
