#!/bin/sh
# module-dependents.sh FIXPT OUT: the costs of `docs/requests/fixpt-module-type-per-dependent.md`.
# Each case is a maker a.fx, given to N makers b1.fx … bN.fx, run from
# .fasl's compiled by FIXPT; the median of 20 runs of `FIXPT run main.fx`.
#   src-M     a.fx defines M procedures of distinct types itself (a large source)
#   lib-M     a.fx loads lib.fx, which defines them (a small source, a large type)
#   same-M    as lib-M, the M types all the same
#   hidden-M  as lib-M, the load in a `hide`
#   mono-M    as lib-M, the procedures monomorphic
# Each is run at N = 0 and N = 20; (t20 - t0) / 20 is a dependent's cost.
fixpt=${1:?FIXPT}; out=${2:?OUT}; mkdir "$out" || exit 1; cd "$out" || exit 1
proc() { # proc I KIND: procedure fI; KIND poly (distinct), same (poly, one type), mono (distinct)
  case $2 in
    poly) echo "(define f$1 (poly ((p place) (a type) (e effect) (r region)) (subr (maxeff e (read (acyclic p)) (alloc r)) ((subr e (a) a) (listof a (acyclic p))) (listof (productof (k$1 a)) r))) (plambda ((p place) (a type) (e effect) (r region)) (lambda (f l) (the (listof (productof (k$1 a)) r) nil))))";;
    same) echo "(define f$1 (poly ((p place) (a type) (e effect) (r region)) (subr (maxeff e (read (acyclic p)) (alloc r)) ((subr e (a) a) (listof a (acyclic p))) (listof a r))) (plambda ((p place) (a type) (e effect) (r region)) (lambda (f l) (the (listof a r) nil))))";;
    mono) echo "(define f$1 (subr pure (int (listof int acyclic)) (productof (k$1 int))) (lambda (x l) (product (k$1 x))))";;
  esac; }
procs() { i=1; while [ $i -le $1 ]; do proc $i $2; i=$((i+1)); done; }
make() { # make DIR SHAPE M N
  mkdir "$1" && cd "$1" || exit 1
  echo '(define zero int 0)' > z.fx
  echo '(module-parameters ((z (load-moduleof "z.fx"))))' > a.fx
  case $2 in
    src)    procs $3 poly >> a.fx;;
    lib)    procs $3 poly > lib.fx; echo '(define kl (load-module "lib.fx"))' >> a.fx;;
    same)   procs $3 same > lib.fx; echo '(define kl (load-module "lib.fx"))' >> a.fx;;
    mono)   procs $3 mono > lib.fx; echo '(define kl (load-module "lib.fx"))' >> a.fx;;
    hidden) procs $3 poly > lib.fx; echo '(hide (define kl (load-module "lib.fx")))' >> a.fx;;
  esac
  echo '(define one int (+ zero 1))' >> a.fx
  printf '(define z (load-module "z.fx"))\n(define a ((load-module "a.fx") z))\n' > main.fx
  i=1; while [ $i -le $4 ]; do
    printf '(module-parameters ((z (load-moduleof "z.fx")) (a (load-moduleof "a.fx" z))))\n(define v%d int (+ one %d))\n' $i $i > b$i.fx
    echo "(define b$i ((load-module \"b$i.fx\") z a))" >> main.fx; i=$((i+1)); done
  echo 1 >> main.fx
  libs=; [ -e lib.fx ] && libs=lib.fx
  "$fixpt" compile-file z.fx $libs a.fx $(ls b*.fx 2>/dev/null) > compile.log 2>&1 || echo "compile failed: $1"
  "$fixpt" run main.fx > /dev/null 2>&1 || echo "run failed: $1"
  cd ..; }
median() { # median DIR: the median ms of 20 runs
  python3 -c '
import subprocess,sys,time,statistics
ts=[]
for _ in range(20):
    t=time.perf_counter(); subprocess.run(sys.argv[1:],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL); ts.append((time.perf_counter()-t)*1000)
print(f"{statistics.median(ts):.1f}")' "$fixpt" run "$1/main.fx"; }
"$fixpt" prewarm > /dev/null 2>&1
printf '%-10s %8s %8s %12s\n' case "N=0 ms" "N=20 ms" "ms/dependent"
for c in none-0 src-80 lib-20 lib-80 same-80 mono-80 hidden-80; do
  shape=${c%-*}; m=${c#*-}; [ "$shape" = none ] && shape=lib
  make $c-0 $shape $m 0; make $c-20 $shape $m 20
  t0=$(median $c-0); t20=$(median $c-20)
  printf '%-10s %8s %8s %12s\n' $c $t0 $t20 $(python3 -c "print(f'{($t20-$t0)/20:.2f}')")
done
