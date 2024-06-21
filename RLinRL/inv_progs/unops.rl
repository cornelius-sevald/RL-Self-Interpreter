(a b c yess nos) -> (a b c) with (nums)

in:
	fi !(a)
		from yes1
		else no1
	nos ^= '0
	yess ^= '0
	nums ^= '(1.(2.4))
	exit

yes1:
	from mid1
	yess -= hd(nums)
	goto in

no1:
	from mid1
	nos -= hd(nums)
	goto in

mid1:
	fi !(!(b))
		from yes2
		else no2
	if !(a)
		goto yes1
		else no1

yes2:
	from mid2
	yess -= hd(tl(nums))
	goto mid1

no2:
	from mid2
	nos -= hd(tl(nums))
	goto mid1

mid2:
	fi !(!(!(c)))
		from yes3
		else no3
	if !(!(b))
		goto yes2
		else no2

yes3:
	from out
	yess -= tl(tl(nums))
	goto mid2

no3:
	from out
	nos -= tl(tl(nums))
	goto mid2

out:
	entry
	nums ^= '(1.(2.4))
	if !(!(!(c)))
		goto yes3
		else no3
