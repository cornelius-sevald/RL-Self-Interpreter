(n) -> (a b)

init:
entry
  a ^= '0
  b ^= '1
if n = '0 goto stop else loop

loop:
fi a = '0 from init else loop
  n -= '1
  (a . b) <- (b . a)
  b += a
if n = '0 goto stop else loop

stop:
fi a = '0 from init else loop
  n ^= '0
exit
