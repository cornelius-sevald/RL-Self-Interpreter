(a b c) -> (a b c)

in:
	from mid
	exit

mid:
	from out
	c -= (a + b)
	b -= (a + c)
	a -= (b + c)
	goto in

out:
	entry
	goto mid
