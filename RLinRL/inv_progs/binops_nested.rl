(a b c) -> (a b c)

in:
	from mid
	exit

mid:
	from out
	c -= ((a * b) + ((b / (a * '2)) - a))
	b -= ((a * c) + ((c / (a * '2)) - a))
	a -= ((b * c) + ((c / (b * '2)) - b))
	goto in

out:
	entry
	goto mid
