(a b) -> (n)

init:
	fi (n = '0)
		from stop
		else loop
	b ^= '1
	a ^= '0
	exit

loop:
	fi (n = '0)
		from stop
		else loop
	b -= a
	(b . a) <- (a . b)
	n += '1
	if (a = '0)
		goto init
		else loop

stop:
	entry
	n ^= '0
	if (a = '0)
		goto init
		else loop
