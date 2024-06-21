(c) -> (c)

in:
	fi c
		from yes
		else no
	exit

yes:
	from out
	goto in

no:
	from out
	goto in

out:
	entry
	if c
		goto yes
		else no
