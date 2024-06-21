(a b c yess nos) -> (a b c)

in:
	fi a
		from yes1
		else no1
	nos ^= '0
	yess ^= '0
	exit

yes1:
	from mid1
	yess -= '1
	goto in

no1:
	from mid1
	nos -= '1
	goto in

mid1:
	fi b
		from yes2
		else no2
	if a
		goto yes1
		else no1

yes2:
	from mid2
	yess -= '1
	goto mid1

no2:
	from mid2
	nos -= '1
	goto mid1

mid2:
	fi c
		from yes3
		else no3
	if b
		goto yes2
		else no2

yes3:
	from out
	yess -= '1
	goto mid2

no3:
	from out
	nos -= '1
	goto mid2

out:
	entry
	if c
		goto yes3
		else no3
