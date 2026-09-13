#!/usr/bin/env bash
# Per-package line counts for two checkouts, side by side, with deltas.
#
# "It got smaller" is a claim about a tree, and a claim about a tree should be
# checkable in one command.  This prints src/main and src/test lines per Java
# package for two repositories, the delta between them, and each side's test
# count, so a round's report can be read against the trees it describes rather
# than against remembered numbers.
#
# Usage: tools/linecount_reconcile.sh <repo A> <repo B>
set -uo pipefail

if [[ $# -ne 2 ]]; then
  sed -n '2,12p' "$0" | sed 's/^# \{0,1\}//'
  exit 2
fi

a=$1
b=$2
for repo in "${a}" "${b}"; do
  [[ -d "${repo}/src/main/java" ]] \
    || { echo "not a checkout: ${repo}" >&2; exit 2; }
done

# package -> total lines, for one tree, as "<package> <lines>" rows.
package_lines() {
  local root=$1 tree=$2
  [[ -d "${root}/src/${tree}/java" ]] || return 0
  find "${root}/src/${tree}/java" -name '*.java' -print0 \
    | xargs -0 wc -l 2>/dev/null \
    | awk -v root="${root}/src/${tree}/java/" '
        $2 != "total" {
          path = $2
          sub(root, "", path)
          sub(/\/[^\/]*$/, "", path)
          gsub(/\//, ".", path)
          sub(/^edu\.uva\.liftlab\.graphchecker\.?/, "", path)
          if (path == "") path = "(root)"
          lines[path] += $1
        }
        END { for (name in lines) print name, lines[name] }'
}

table() {
  local tree=$1
  echo
  echo "src/${tree}"
  printf '%-28s %10s %10s %10s\n' "package" "A" "B" "delta"
  printf '%-28s %10s %10s %10s\n' \
    "----------------------------" "----------" "----------" "----------"
  {
    package_lines "${a}" "${tree}" | sed 's/^/A /'
    package_lines "${b}" "${tree}" | sed 's/^/B /'
  } | awk '
      $1 == "A" { first[$2] = $3; seen[$2] = 1 }
      $1 == "B" { second[$2] = $3; seen[$2] = 1 }
      END {
        n = 0
        for (name in seen) { order[n++] = name }
        for (i = 0; i < n; i++) {
          for (j = i + 1; j < n; j++) {
            if (order[j] < order[i]) { t = order[i]; order[i] = order[j]; order[j] = t }
          }
        }
        for (i = 0; i < n; i++) {
          name = order[i]
          x = first[name] + 0
          y = second[name] + 0
          delta = y - x
          totalA += x
          totalB += y
          printf "%-28s %10d %10d %+10d\n", name, x, y, delta
        }
        printf "%-28s %10d %10d %+10d\n", "TOTAL", totalA, totalB, totalB - totalA
      }'
}

# Every @Test in the tree: the number a suite run should report.
test_count() {
  local root=$1
  [[ -d "${root}/src/test/java" ]] || { echo 0; return; }
  grep -rho '@Test' "${root}/src/test/java" 2>/dev/null | wc -l
}

test_classes() {
  local root=$1
  [[ -d "${root}/src/test/java" ]] || { echo 0; return; }
  find "${root}/src/test/java" -name '*Test.java' | wc -l
}

echo "A = ${a}"
echo "B = ${b}"
table main
table test
echo
printf '%-28s %10s %10s %10s\n' "tests" "A" "B" "delta"
printf '%-28s %10d %10d %+10d\n' "@Test methods" \
  "$(test_count "${a}")" "$(test_count "${b}")" \
  "$(( $(test_count "${b}") - $(test_count "${a}") ))"
printf '%-28s %10d %10d %+10d\n' "test classes" \
  "$(test_classes "${a}")" "$(test_classes "${b}")" \
  "$(( $(test_classes "${b}") - $(test_classes "${a}") ))"
