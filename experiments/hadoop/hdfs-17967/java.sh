#!/usr/bin/env bash
# The engine JVM.  CAUSYNTH_CLOCK_SKEW_WINDOW_MS, when set, states a forward
# clock window other than JavaPrimitiveSmtSemantics' 30-day default.  It is
# what decides whether a flipped key-refresh RPC is NECESSARY: a key retires
# at mint + keyUpdateInterval + tokenLifetime and the one that replaces it at
# mint + 2*keyUpdateInterval + tokenLifetime, so a window between the two lets
# a clock expire the STALE key and not the fresh one -- and then only the
# marker can put the stale key on the wire.  Unset, nothing changes.
exec /usr/lib/jvm/java-8-openjdk-amd64/bin/java -Xmx8g \
  ${CAUSYNTH_CLOCK_SKEW_WINDOW_MS:+-Dcausynth.clock.skew.window.ms=$CAUSYNTH_CLOCK_SKEW_WINDOW_MS} \
  "$@"
