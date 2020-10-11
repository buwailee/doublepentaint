# Copyright (C) 2014 Erik Panzer
#
#   This program is free software: you can redistribute it and/or modify
#   it under the terms of the GNU General Public License as published by
#   the Free Software Foundation, either version 3 of the License, or
#   (at your option) any later version.
#
#   This program is distributed in the hope that it will be useful,
#   but WITHOUT ANY WARRANTY; without even the implied warranty of
#   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#   GNU General Public License for more details.
#
#   You should have received a copy of the GNU General Public License
#   along with this program.  If not, see <http://www.gnu.org/licenses/>.
#
# To contact the author, please use panzer@mathematik.hu-berlin.de
#
# Implements the algorithm originally described in
#
# 	F. Brown, The Massless Higher-Loop Two-Point Function,
# 	Communications in Mathematical Physics 287 (2009) 925–958.
# 	arXiv:0804.1660, doi:10.1007/s00220-009-0740-5.
#
# for the parametric integration of Feynman integrals and the
# compatibility-graph method of polynomial reduction introduced in
#
# 	F. Brown, On the periods of some Feynman integrals, arXiv:0910.0114.

interface(errorbreak=2, warnlevel=4):

# If set to true, some progress information is printed during calculation
_hyper_verbosity := 1:
_hyper_verbose_frequency := 10:

# If set to true, divergences at the integration limits towards zero and infinity are calculated and checked to vanish
_hyper_check_divergences := true:
_hyper_abort_on_divergence := true:
# List to collect the accumulated conditions for all divergences to cancel
_hyper_divergences := table():

# This field is used as domain for factorizations of all polynomials! In cases of ramifications, the radicals are to be put here
_hyper_splitting_field := {}:
# if set to true, all polynomials will be factored (introducing algebraic functions for the roots, i.e. prohibiting further integration of the result obtained!)
_hyper_algebraic_roots := false:
_hyper_ignore_nonlinear_polynomials := false:
# This enables to discard any singularities not in a predescribed domain; here we can put in results from some polynomial reduction
_hyper_restrict_singularities := false:
_hyper_allowed_singularities := {}:

# For polynomial reduction: do not use factor, but look for divisors in the upper bound of factors instead
_hyper_use_factor_bounds := true:

_hyper_max_pole_order := 10:

# if set to true, return results as the tables which they are internally, otherwise transform to a list representation
_hyper_return_tables := false:

# General purpose storage
_hyper_scratch := Array(1..10000):

# To allow for setting the path to the period Lookups via initialization files, check for assignment first
if not assigned(_hyper_autoload_periods) then
	_hyper_autoload_periods := ["periodLookups.m"]:
end if:

# When set to true, partial fractioning is implemented as a linear map
# This helps for cases when polynomials with higher powers appear in denominators
# (experimental)
_hyper_additive_parfrac := false:

printf("HyperInt, version 1.0, Copyright (C) 2014 Erik Panzer\n"):
printf("Please report any errors or suggestions to panzer@mathematik.hu-berlin.de\n"):

with(PolynomialTools, FromCoefficientList):

# Do not keep entries with value zero
`index/sparsereduced` := proc(Idx::list, Tbl::table, Entry::list)
local val:
	if (nargs = 2) then
		if assigned(Tbl[op(Idx)]) then Tbl[op(Idx)]:
		else 0: end if:
	else
		val := normal(Entry[1]):
		if val = 0 then
			Tbl[op(Idx)] := evaln(Tbl[op(Idx)]):
		else
			Tbl[op(Idx)] := val:
		end if:
		val:
	end if:
end proc:

# When dealing with long polynomials, ommit normal() in indexing function
if _hyper_additive_parfrac then
`index/sparsereduced` := proc(Idx::list, Tbl::table, Entry::list)
local val:
	if (nargs = 2) then
		if assigned(Tbl[op(Idx)]) then Tbl[op(Idx)]:
		else 0: end if:
	else
		val := Entry[1]:
		if val = 0 then
			Tbl[op(Idx)] := evaln(Tbl[op(Idx)]):
		else
			Tbl[op(Idx)] := val:
		end if:
		val:
	end if:
end proc:
end:

forgetAll := proc ()
global _hyper_divergences:
	_hyper_divergences := table():
	forget(transformWord):
	forget(partialFractions):
	forget(poledegree):
	forget(linearFactors):
	forget(reglimWord):
	forget(regzeroWord):
	forgetExpansions():
	forget(myfactors):
	forget(shuffleWords):
	# Important: Initialize shuffleWords' remember table, as op(4, op(shuffleWords)) is otherwise not assigned (it is nothing instead of an empty table), so the check assirgned(...[w,v]) throws an error if it is empty!
	shuffleWords([],[]) := [[]]:
end proc:

###################################################################################################################
# Elementary operations on lists of words: collect (addition), concatenation product, shuffle product
###################################################################################################################

collectWords := proc (wordlist)
local w, result:
	result := table(sparsereduced):
	for w in wordlist do
		result[w[2]] := result[w[2]] + w[1]:
	end do:
	[seq([normal(rhs(w)),lhs(w)], w in indices(result, 'pairs'))]:
end proc:

# Insertion Sort
addInplace := proc (place, count, poly, param)
local i, found:
	# param already in the list?
	found := false:
	for i from 1 to count do
		if place[i][2] = param then found := true: break: end if:
	end do:
	if not found then
		place[count+1] := [poly, param]:
		return (count+1):
	end if:
	# Zero coefficient?
	place[i][1] := normal(place[i][1]+poly):
	if place[i][1] = 0 then
		place[i] := place[count]:
		return (count-1):
	end if:
	count:
end proc:

# Returns a list of words (no factors!)
shuffleWords := proc (v, w)
local u:
option remember:
	if w = [] then
		[v]:
	elif v = [] then
		[w]:
	elif assigned(op(4, op(shuffleWords))[w,v]) then
		# Exploit symmetry for remember table
		op(4, op(shuffleWords))[w,v]:
	else	
		[seq([v[1], op(u)], u in shuffleWords(v[2 .. nops(v)], w)),seq([w[1], op(u)], u in shuffleWords(v, w[2 .. nops(w)]))]:
	end if:
end proc:
# Important: Initialize shuffleWords' remember table, as op(4, op(shuffleWords)) is otherwise not assigned (it is nothing instead of an empty table), so the check assigned(...[w,v]) throws an error if it is empty!
shuffleWords([],[]) := [[]]:

shuffleList := proc (a, b)
local i, j, count, w:
global _hyper_scratch:
	count := 0:
	for i in a do
		for j in b do
			for w in shuffleWords(i[2], j[2]) do
				count := addInplace(_hyper_scratch, count, i[1]*j[1], w):
			end do:
		end do:
	end do:
	[seq(_hyper_scratch[i], i=1..count)]:
end proc:

shuffle := proc (a, b)
local result:
	# Use list-based implementation only for short results
	if (nops(a)*nops(b))<10 then
		return shuffleList(a, b):
	end if:
	result := table(sparsereduced):
	shuffleTo(a, b, result):
	[seq([rhs(i), lhs(i)], i in indices(result, 'pairs'))]:
end proc:

shuffleTo := proc (a, b, result)
local u, v, w:
	for u in a do
		for v in b do
			for w in shuffleWords(u[2], v[2]) do
				result[w] := result[w] + u[1]*v[1]:
			end do:
		end do:
	end do:
end proc:

Mul := proc (a, b)
local i, j, result, w:
	# Use list-based implementation only for short results
	if (nops(a)*nops(b))<10 then
		return MulList(a, b):
	end if:
	result := table(sparsereduced):
	for i in a do
		for j in b do
			w := [op(i[2]),op(j[2])]:
			result[w] := result[w] + i[1]*j[1]:
		end do:
	end do:
	[seq([normal(rhs(w)),lhs(w)], w in indices(result, 'pairs'))]:
end proc:

MulList := proc (a, b)
local i,j:
	[seq(seq([i[1]*j[1], [op(i[2]), op(j[2])]], i in a), j in b)]:
end proc:

scalarMul := proc (wordlist, c)
	[seq([w[1]*c, w[2]], w in wordlist)]:
end proc:

shuffleSymbolic := proc (A, B)
local i, j, result, L:
	result := table(sparsereduced):
	for i in A do
		for j in B do
			L := sort([op(i[2]), op(j[2])]):
			result[L] := result[L] + i[1]*j[1]:
		end do:
	end do:
	return [seq([rhs(L), lhs(L)], L in indices(result, 'pairs'))]:
end proc:

shuffleSymbolicTo := proc (A, B, result)
local i, j, L:
	for i in A do
		for j in B do
			L := sort([op(i[2]), op(j[2])]):
			result[L] := result[L] + i[1]*j[1]:
		end do:
	end do:
end proc:

###########################################################################################################################
# Computing regularized limits
###########################################################################################################################

# Computes the vanishing degree of the rational function p at var->0
# This is the leading power of var in the Laurent series of p(var)
poledegree := proc (p, var)
local deg, f:
option remember:
	f := normal(p):
	deg := ldegree(numer(f), var):
	if deg=0 then
		deg := -ldegree(denom(f), var):
	end if:
	deg:
end proc:

# Computes the leading coefficient g(0) of the Laurent series f(var) = var^n * g(var) where g(0)<>0 is finite
ratResidue := proc (f, var)
local p, q:
	p := numer(f):
	q := denom(f):
	if p=0 then
		error "zero-polynomial %1 not allowed", f:
	end if:
	normal(tcoeff(p, var)/tcoeff(q, var)):
end proc:

# Calculate RegLim_{var->0} of RegInf(wordlist)
reglim := proc (wordlist, var)
local result, w, v:
	result := table(sparsereduced):
	for w in wordlist do
		for v in reglimWord(w[2], var) do
			result[v[2]] := result[v[2]] + v[1]*w[1]:
		end do:
	end do:
	[seq([rhs(v), lhs(v)], v in indices(result, 'pairs'))]:
end proc:

# Calculates a word u such that RegLim_{var->0} Reginf (word) = Reginf (u)
reglimWord := proc (word::list, var)
option remember:
global _hyper_verbosity:
local i, n, minOrder, zeroOrders, result, w, onAxis, scaled, origin, temp:
	if word = [] then
		return [[1, []]]:
	end if:
	# Word consisting of only {0} or {-1} does not contribute to reginf = reginf & reg0
	if {op(word)} in {{0}, {-1}} then
		return []:
	end if:
	zeroOrders := map(poledegree, word, var):
	minOrder := min(zeroOrders):
	result := table(sparsereduced):
	w := numelems(word):
	# Count and shuffle off the trailing letters approaching zero
	n := 0:
	while zeroOrders[w-n]>minOrder do
		n := n+1:
	end do:
	if n > 0 then 
		for i from 0 to n do
			temp := []:
			for scaled in regzeroWord([op(1..w-n, word), 0$i]) do
				temp := [op(temp), op(scalarMul(reglimWord(scaled[2], var), scaled[1]))]:
			end do:
			shuffleSymbolicTo(collectWords(temp), reglimWord(word[w-n+1+i..w], var), result):
		end do:
		return [seq([rhs(z), lhs(z)], z in indices(result, 'pairs'))]:
	end if:
	# after rescaling by var^(-minOrder), perform limit of letters
	scaled := []:
	onAxis := table():
	for i from 1 to w do
		if zeroOrders[i]>minOrder then
			scaled := [op(scaled), 0]:
		else
			scaled := [op(scaled), ratResidue(word[i], var)]:
			# Letters approaching positive real axis: coming from above (+1) or below (-1) ?
			if type(scaled[i], positive) then
				if minOrder>0 then
					origin := delta[var]:
				elif minOrder<0 then
					origin := -delta[var]:
				else
					# Next to leading coefficient in the Laurent series var->0
					origin := ratResidue(word[i]*var^(-minOrder)-scaled[i], var):
					if Im(origin)<> 0 then
						origin := signum(Im(origin)):
					else
						origin := signum(Re(origin))*delta[var]:
					end if:
				end if:
				if not assigned(onAxis[scaled[i]]) then
					onAxis[scaled[i]] := origin:
				elif onAxis[scaled[i]]<>origin then
					error "Pinch-singularity not implemented; need %1=%2", onAxis[scaled[i]], origin:
				end if:
			end if:
		end if:
	end do:
	onAxis := sort([entries(onAxis, pairs)], (a,b)->lhs(a)<lhs(b)):
	if _hyper_verbosity>99 then
		print(scaled, onAxis):
	end if:
	# With positive letters, reexpress deformed integration contour as [0,infinity)
	return breakUpContour([[1, scaled]], onAxis):
end proc:

# wordList is a reg_{z \rightarrow \inty} Hlog_w(gamma) for a path gamma from 0 to infinity such that the positive letters lie above (below) gamma as specified
# returns the same value but represented as periods with the straight contour 0->infinity, i.e. without positive letters
breakUpContour := proc(wordList::list, onAxis::list)
local smallest, i, w, temp, word, result, imPart, newAxis:
	if numelems(onAxis) = 0 then
		# For efficiency, replace periods if possible
		temp, result := selectremove(word->{op(word[2])} subset {-2,-1,0}, wordList):
		temp := `+`(op(map(word -> word[1]*zeroInfPeriod(word[2]), temp))):
		result := map(word->[word[1],`if`(word[2]=[], [], [word[2]])], result):
		if temp<>0 then
			return [[temp,[]], op(result)]:
		else
			return result:
		end if:
	end if:
	result := table(sparsereduced):
	smallest, imPart := op(onAxis[1]):
	newAxis := [seq(lhs(onAxis[i])-smallest = rhs(onAxis[i]), i=2..nops(onAxis))]:
	for word in wordList do
		w := numelems(word[2]):
		for i from 0 to w do
			# For efficiency, replace periods if possible
			temp := word[2][i+1..w]:
			if (smallest=1) and (indets(temp)={}) then
				temp := [[zeroOnePeriod(temp), []]]:
			else
				temp := convertABtoZeroInf(reghead([[1, temp]], smallest), 0, smallest):
				temp :=	map(v->[v[1],`if`(v[2]=[], [], [v[2]])], temp):
			end if:
			shuffleSymbolicTo(
					breakUpContour(
							regtail([[word[1], map(v->v-smallest, word[2][1..i])]], 0, Pi*I*imPart - ln(smallest)),
							newAxis),
					temp,
					result
			):
		end do:
	end do:
	return [seq([rhs(z), lhs(z)], z in indices(result, 'pairs'))]:
end proc:

###########################################################################################################################
# Expressing regularized limits as hyperlogarithms w.r.t. a parameter
###########################################################################################################################

# Transforms wordlist (a list of words meant to be shuffled), representing Reg_infinity(wordlist), into a sum (list) of products (pairs) of a word in var (iterated integral) and a list (representing shuffle product) of words representing Reg_infinity
transformShuffle := proc (wordlist, var)
local result, word, i,  sub, temp, countTemp, count, pair:
	# Empty argument equals one
	if wordlist=[] then
		return [[[[1, []]], [[1, []]]]]:
	end if:
	# Reduce products
	result := Array(1..4000):
	count := 1:
	result[1] := [[[1, []]], [[1, []]]]:
	temp := Array(1..4000):
	for word in wordlist do
		sub := transformWord(word, var):
		countTemp := 0:
		for pair in sub do
			for i from 1 to count do
				countTemp := countTemp+1:
				temp[countTemp] := [collectWords(shuffle(result[i][1],pair[1])), shuffleSymbolic(result[i][2], pair[2])]:
			end do:
		end do:
		i := result:
		result := temp:
		count := countTemp:
		temp := i:
	end do:
	return convert(result[1..count], list, nested):
end proc:

# Takes a single iterated integral and returns a list [[L1, [R11,R12,...]], [L2,[R22,R22,...]],...] of pairs of an iterated integral L1 in var and constant factors reginf(R11)*reginf(R12)*...
transformWord := proc(word, var)
local result, p, i, sub, facts:
global _hyper_verbosity:
option remember:
	if word=[] then
		return ([[[[1, []]], [[1,[]]]]]):
	end if:
	result := table():
	# Integration constants
	sub := reglimWord(word, var):
	if nops(sub)>0 then
		result[sub] := table(sparsereduced, [[]=1]):
	end if:
	if word[nops(word)]=0 then
		error "Word %1 ending on zero", word:
	end if:
	for i from 1 to nops(word) do
		# Do not generate words ending on zero
		if i=nops(word) and i>1 then
			if word[i-1]=0 then
				break:
			end if:
		end if:
		if i<nops(word) then
			p := word[i]-word[i+1]:
		else
			p := word[i]:
		fi:
		p := normal(p):
		if p=0 then next: fi:
		# Find multiplicities of zeros in var
		facts := linearFactors(p, var):
		if nops(facts)=0 then
			next:
		end if:
		# drop the letter i+1
		if (i<nops(word)) then
			p := [op(word[1..i]),op(word[i+2..nops(word)])]:
			# Do not generate words ending on zero
			if p[nops(p)]<>0 then
				for sub in transformWord(p, var) do
					if not assigned(result[sub[2]]) then
						result[sub[2]] := table(sparsereduced):
					end if:
					prependInplace(sub[1], facts, 1, result[sub[2]]):
				end do:
			end if:
		end if:
		# Drop the letter i
		p := [op(word[1..i-1]),op(word[i+1..nops(word)])]:
		for sub in transformWord(p, var) do
			if not assigned(result[sub[2]]) then
				result[sub[2]] := table(sparsereduced):
			end if:
			prependInplace(sub[1], facts, -1, result[sub[2]]):
		end do:
	end do:
	[seq(`if`(numelems(rhs(sub))=0,NULL,[[seq([rhs(p), lhs(p)], p in indices(rhs(sub), 'pairs'))], lhs(sub)]), sub in indices(result, 'pairs'))]:
end proc:

prependInplace := proc (wordlist, poles, fact, result)
local w, p, v:
	for w in wordlist do
		for p in poles do
			v := [p[2], op(w[2])]:
			result[v] := result[v] + p[1]*w[1]*fact:
		end do:
	end do:
end proc:

###########################################################################################################################
# Partial fractioning
###########################################################################################################################

# Maple's factors and factor do not work when constants like Pi multiply a polynomial
fixedfactors := proc(p, field)
local c, g:
	if op(0, p)<>`*` then
		factors(p, field)
	else
		c,g:=selectremove(f->type(f,constant), p):
		g:=factors(g, field):
		g[1]:=g[1]*c:
		g:
	end if:
end proc:

# If p = prod (var - x_i)^n_i, return list [[x_1,n_1], [x_2,n_2], ...]
linearFactors := proc (p, var)
option remember:
local facts, sub, f:
global _hyper_splitting_field, hyper_algebraic_roots, _hyper_ignore_nonlinear_polynomials, _hyper_allowed_singularities, _hyper_restrict_singularities, _hyper_verbosity:
	facts := []:
	for sub in op(2, fixedfactors(p, _hyper_splitting_field)) do
		# Only factors depending on var do contribute here (we search zeros and poles in var)
		if degree(sub[1], var)=0 then next: fi:
		# If supplied, exploit knowledge of the loci of possible singularities
		if _hyper_restrict_singularities then
			if (not (sub[1] in _hyper_allowed_singularities)) then
				if (_hyper_verbosity>0) then
					printf("discarding %a\n", sub[1]):
				end if:
				next:
			end if:
		end if:
		# Linearity check
		if degree(sub[1], var)=1 then
			f:= -coeff(sub[1], var, 0)/coeff(sub[1], var, 1):
		elif _hyper_algebraic_roots then
			f := Root(sub[1], var):
		elif _hyper_ignore_nonlinear_polynomials then
			if _hyper_verbosity>0 then
				printf("discarding nonlinear %a\n", sub[1]):
			end if:
			next:
		else
			error "%1 does not factor linearly in %2\n", sub[1], var:
		end if:
		# This should never occur
		if not (type(f, ratpoly) or _hyper_algebraic_roots) then
			error "%1 is not a polynomial, something went wrong in transformWord", f:
		end if:
		facts := [[sub[2], normal(f)], op(facts)]:
	end do:
	facts:
end proc:

# Convert f into partial fractions in var, returned as a list [p,[a,f1,f2,f3...],[b,g1,g2,g3,...],...]
partialFractions := proc(f, var)
local p, poles, q, z, zero, i, pars, fac, newq:
option remember:
global _hyper_splitting_field, _hyper_additive_parfrac, _hyper_verbosity:
	# Do not combine sums, but work separately:
	if _hyper_additive_parfrac and op(0,f)=`+` then
		p := 0:
		q := []:
		for pars in map(partialFractions, [op(f)], var) do
			# Add polynomial parts
			p := p + pars[1]:
			# Add fractions
			for fac in pars[2..nops(pars)] do
				# search if this zero is already present
				zero := false:
				for i from 1 to nops(q) do
					if q[i][1] = fac[1] then
						zero := i:
						break:
					end if:
				end do:
				# if not found, then add
				if zero=false then
					q := [op(q), fac]:
					next:
				end if:
				# Otherwise, add the lists
				for i from 2 to min(nops(q[zero]), nops(fac)) do
					q[zero][i] := q[zero][i] + fac[i]:
				end do:
				if nops(fac)>nops(q[zero]) then
					q[zero] := [op(q[zero]), op(fac[nops(q[zero])+1..nops(fac)])]:
				end if:
			end do:
		end do:
		return [p, op(q)]:
	end if:
	p := normal(f):
	q := denom(p):
	p := numer(p):
	# Find all zeros of the denominator
	poles := []:
	# Avoid Bug in solve: In some cases it stucks when q does not depend on var...
	if not (var in indets(q)) then
		return [p/q]:
	end if:
	pars := fixedfactors(q, _hyper_splitting_field):
	newq := pars[1]:
	for fac in pars[2] do
		if degree(fac[1], var) = 0 then
			newq := newq*fac[1]^fac[2]:
			next:
		elif degree(fac[1], var) > 1 then
			error "%1 is not linear in %2", fac[1], var:
		end if:
		zero := -coeff(fac[1], var, 0)/coeff(fac[1], var, 1):
		poles := [op(poles), [zero, fac[2], fac[1]]]:
#		newq := newq*coeff(fac[1], var, 1)^fac[2]:
	end do:
	# Convert into partial fracions
	q := newq:
	pars := convert([p, op([seq([z[3], z[2]], z in poles)])], parfrac, var):
	pars[1] := normal(pars[1]/q):
	for i from 1 to nops(poles) do
		if pars[i+1, 1] <> poles[i, 3] then
				error "wrong data structure resulted from convert(parfrac): %1 does not match expected %2", pars[i+1,1], poles[i,3]:
		end if:
		pars[i+1,1] := poles[i,1]:
		for z from 2 to nops(pars[i+1]) do
			pars[i+1, z] := factor(pars[i+1, z]/q/coeff(poles[i,3], var, 1)^(z-1)):
		end do:
	end do:
	pars:
end proc:

###########################################################################################################################
# Integration (constructing primitives)
###########################################################################################################################

integrate := proc (wordlist, var)
local w, result, p, i, parfr, n, v:
global _hyper_verbosity:
	result := table(sparsereduced):
	for w in wordlist do
		parfr := partialFractions(w[1], var):
		if parfr[1] <> 0 then
			p := int(parfr[1], var = 0 .. var):
			result[w[2]] := result[w[2]] + p:
			# Integration by parts: contribution from the derivative of the word
			if 0 < nops(w[2]) then
				integrateInplace(result, [[-p/(var-w[2, 1]), w[2, 2 .. nops(w[2])]]], var):
			end if:
		end if:
		for i from 2 to nops(parfr) do
			for n from 1 to nops(parfr[i])-1 do
				if parfr[i, n+1] = 0 then next end if:
				if 1 < n then
					p := parfr[i, n+1]/((var-parfr[i, 1])^(n-1)*(1-n)):
					result[w[2]] := result[w[2]] + p:
					# Integration by parts: contribution from the derivative of the word
					if 0 < nops(w[2]) then
						integrateInplace(result, [[-p/(var-w[2, 1]), w[2, 2 .. nops(w[2])]]], var):
					end if:
				end if:
				if n = 1 then
					v := [parfr[i, 1], op(w[2])]:
					result[v] := result[v] + parfr[i, n+1]:
				end if:
			end do:
		end do:
	end do:
	[seq([rhs(w), lhs(w)], w in indices(result, 'pairs'))]:
end proc:

integrateInplace := proc (result, wordlist, var)
local w, p, i, parfr, n, v:
global _hyper_verbosity:
	for w in wordlist do
		parfr := partialFractions(w[1], var):
		if parfr[1] <> 0 then
			p := int(parfr[1], var = 0 .. var):
			result[w[2]] := result[w[2]] + p:
			# Integration by parts: contribution from the derivative of the word
			if 0 < nops(w[2]) then
				integrateInplace(result, [[-p/(var-w[2, 1]), w[2, 2 .. nops(w[2])]]], var):
			end if:
		end if:
		for i from 2 to nops(parfr) do
			for n from 1 to nops(parfr[i])-1 do
				if parfr[i, n+1] = 0 then next end if:
				if 1 < n then
					p := parfr[i, n+1]/((var-parfr[i, 1])^(n-1)*(1-n)):
					result[w[2]] := result[w[2]] + p, w[2]:
					# Integration by parts: contribution from the derivative of the word
					if 0 < nops(w[2]) then
						integrateInplace(result, [[-p/(var-w[2, 1]), w[2, 2 .. nops(w[2])]]], var):
					end if:
				end if:
				if n = 1 then
					v := [parfr[i, 1], op(w[2])]:
					result[v] := result[v] + parfr[i, n+1]:
				end if:
			end do:
		end do:
	end do:
end proc:

###########################################################################################################################
# Expansions at zero and infinity
###########################################################################################################################

# Computes the Laurent series of ratPoly w.r.t. var->0 up to and including terms of maxOrder
seriesExpansion := proc(ratPoly, var, maxOrder:=0)
local result, calcOrder:
	if op(0, ratPoly) = `+` then
		return map(seriesExpansion, ratPoly, var, maxOrder):
	end if:
	calcOrder := maxOrder+2:
	result := series(normal(ratPoly), var=0, calcOrder):
	while order(result)<=maxOrder do
		calcOrder := calcOrder + 10:
		if calcOrder>40 then
			error "Could not expand to required order %1 in %2; only got %3 for %4", maxOrder, var, order(result)-1, ratPoly:
		end if:
		result := series(normal(ratPoly), var=0, calcOrder):
	end do:
	result := convert(result, polynom, var):
	add(var^n*coeff(result,var,n), n=ldegree(result, var)..maxOrder):
end proc:

expandInfListInplace := proc (poles, reginfs, wordlist, var)
local w, i, sub, logpower, power, part, v, L, allone, minOrder, poly, temp, q:
global _hyper_check_divergences:
	for w in wordlist do
		poly := eval(w[1], var = 1/var):
		minOrder := -poledegree(poly, var):
		if minOrder<0 then next: fi:
		# If _hyper_check_divergences=false, then infExpansion gives zero whenever w[2][1..i] <> [], so we do not need to loop at all!
		if (minOrder=0) and (not _hyper_check_divergences) then
			# If the RegLim_{infinity}-part consists only of -1, we can stop
			if w[2]=[(-1)$(nops(w[2]))] then
				next:
			end if:
			v := regzeroWord(w[2]):
			if nops(v)=0 then next: fi:
			# In shuffle representation: normalize first coefficients to one and put constants into the first component of the pair
			sub := subs(var=0, normal(poly)):
			for temp in v do
			for q in reginfs do
				if (temp[2]=[]) then
					L := q[2]:
				else
					L := sort([temp[2],op(q[2])]):
				end if:
				poles[0, 0][L] := poles[0, 0][L] + sub*temp[1]*q[1]:
			end do:
			end do:
			next:
		end if:
		# Deconcatenation-Coproduct
#		poly := convert(series(poly, var = 0), polynom, var):
		poly := seriesExpansion(poly, var):
		allone := true:
		for i from nops(w[2]) to 0 by -1 do
			# If the RegLim_{infinity}-part consists only of -1, we can stop
			if (i<nops(w[2])) then
				allone := allone and (w[2, i+1]=-1):
				if allone then next: end if:
			end if:
			part := infExpansion(w[2][1..i], minOrder):
			v := regzeroWord(w[2, i+1 .. nops(w[2])]):
			if nops(v)=0 then next: fi:
			# In shuffle representation: normalize first coefficients to one and put constants into the first component of the pair
			for logpower from 0 to nops(part)-1 do
				sub := FromCoefficientList(part[logpower+1], var)*poly:
				for power from 0 to minOrder do
					for temp in v do
					for q in reginfs do
						if (temp[2]=[]) then
							L := q[2]:
						else
							L := sort([temp[2],op(q[2])]):
						end if:
						poles[logpower, power][L] := poles[logpower, power][L] + coeff(sub, var, -power)*temp[1]*q[1]:
					end do:
					end do:
					if not _hyper_check_divergences then break: fi:
				end do:
				if not _hyper_check_divergences then break: fi:
			end do:
		end do:
	end do:
end proc:

expandInfWord := proc (word, minOrder)
local sub, result, maxlog, power, logpower, maxpowers, p, i:
	# Start of induction is the empty word; the only one contributing at zero
	if word=[] then
		return [[1]]:
	end if:
	if minOrder<0 then
		return []:
	end if:
	# Inductive Step: calculate expansion of tail
	sub := infExpansion(word[2..nops(word)], minOrder):
	maxlog := nops(sub):
	maxpowers := Array(0..maxlog, 0):
	result := Array(0..maxlog, 0..minOrder, 0):
	# Integrate the first letter
	for logpower from 0 to maxlog-1 do
		# Raising of logarithm power comes only from int ( - dz/z )* log(z)^logpower/(logpower!)
		if sub[logpower+1]<>[] then
			result[logpower+1, 0] := result[logpower+1, 0] - sub[logpower+1][1]
		end if:
		# Remaining integrands are (log z)^n/n! * z^m for m>=0 only, so they only lower the log-powers
		for power from 0 to minOrder-1 do
			# Contribution from -\omega_0
			if power+1<=nops(sub[logpower+1])-1 then
				p := -sub[logpower+1][power+2]:
			else
				p := 0:
			end if:
			# Contribution from \omega_{1/\sigma} for sigma = word[1]
			if word[1]<>0 then
				for i from 0 to min(power, nops(sub[logpower+1])-1) do
					p := p - sub[logpower+1][i+1]*(word[1])^(power-i+1):
				end do:
			end if:
			# Integrate!
			if p=0 then next: fi:
			p := -p:
			for i from logpower to 0 by -1 do
				p := -p/(power+1):
				result[i, power+1] := result[i, power+1] + p:
				maxpowers[i] := power+1:
			end do:
		end do:
	end do:
	# Remove empty entries
	for logpower from 0 to maxlog do
		while maxpowers[logpower]>=0 do
			if result[logpower, maxpowers[logpower]] = 0 then
				maxpowers[logpower] := maxpowers[logpower] - 1:
			else
				break:
			end if:
		end do:
	end do:
	while maxlog>=0 do
		if maxpowers[maxlog] = -1 then
			maxlog := maxlog-1:
		else
			break:
		end if:
	end:
	[seq([seq(result[logpower, power], power=0..maxpowers[logpower])], logpower=0..maxlog)]:
end proc:

expandZeroListInplace := proc (poles, reginfs, wordlist, var)
local w, sub, poly, minOrder, logpower, power, v:
	for w in wordlist do
		minOrder := -poledegree(w[1], var):
		if minOrder < 0 then next end if:
		sub := zeroExpansion(w[2], minOrder):
		for logpower from 0 to nops(sub)-1 do
#			poly := FromCoefficientList(sub[logpower+1], var)*convert(series(w[1], var = 0), polynom, var):
			poly := FromCoefficientList(sub[logpower+1], var)*seriesExpansion(w[1], var):
			for power from 0 to minOrder do
				for v in reginfs do
					poles[logpower, power][v[2]] := poles[logpower, power][v[2]] - coeff(poly, var, -power)*v[1]:
				end do:
				if (not _hyper_check_divergences) then break: fi:
			end do:
			if (not _hyper_check_divergences) then break: fi:
		end do:
	end do:
end proc:

# Returns expansion of word near infinity as [[a_0,0, a_0,1, ...], [a_1,0, a_1,1, ...], ...] such that word(1/z) = sum_{i,j} log(z)^i/i! * z^j a_{i,j} + O(z^{minOrder+1})
infExpansion := proc(word, minOrder)
global _hyper_inf_expansion, _hyper_check_divergences:
	if minOrder<0 then
		return []:
	end if:
	if word=[] then
		return [[1]]:
	end if:
	# All non-empty words have either logarithms or powers of z in the expansion!
	if (minOrder=0) and (_hyper_check_divergences=false) then
		return []:
	end if:
	# If already calculated to sufficient order, return stored result
	if assigned(_hyper_inf_expansion[word]) then
		if _hyper_inf_expansion[word][2] >= minOrder then
			return _hyper_inf_expansion[word][1]:
		end if:
	end if:
	# Otherwise compute and remember the result in the global table
	_hyper_inf_expansion[word] := [expandInfWord(word, minOrder), minOrder]:
	_hyper_inf_expansion[word][1]:
end proc:

# Returns expansion of word near zero as [[a_0,0, a_0,1, ...], [a_1,0, a_1,1, ...], ...] such that word(z) = sum_{i,j} log(z)^i/i! * z^j a_{i,j} + O(z^{minOrder+1})
zeroExpansion := proc(word, minOrder)
local w:
global _hyper_zero_expansion:
	if minOrder<0 then
		return []:
	end if:
	if word=[] then
		return [[1]]:
	end if:
	# All non-empty words have either logarithms or powers of z in the expansion!
	if (minOrder=0) and (_hyper_check_divergences=false) then
		return []:
	end if:
	# If already calculated to sufficient order, return stored result
	w := _hyper_zero_expansion[word]:
	if type(w, list) then
		if w[2] >= minOrder then
			return w[1]:
		end if:
	end if:
	# Otherwise compute and remember the result in the global table
	_hyper_zero_expansion[word] := [expandZeroWord(word, minOrder), minOrder]:
	_hyper_zero_expansion[word][1]:
end proc:

_hyper_zero_expansion	:= table():
_hyper_inf_expansion	:= table():

forgetExpansions := proc()
global _hyper_zero_expansion, _hyper_inf_expansion:
	_hyper_zero_expansion	:= table():
	_hyper_inf_expansion	:= table():
end proc:

expandZeroWord := proc (word, minOrder)
local sub, result, maxlog, power, logpower, maxpowers, p, i:
	if minOrder < 0 then
		return []:
	end if:
	if word=[] then
		return [[1]]:
	end if:
	# Inductive Step: calculate expansion of tail
	sub := zeroExpansion(word[2..nops(word)], minOrder):
	maxlog := nops(sub):
	maxpowers := Array(0..maxlog, 0):
	result := Array(0..maxlog, 0..minOrder, 0):
	# Integrate the first letter
	for logpower from 0 to maxlog-1 do
		# Raising of logarithm power comes only from int ( dz/z )* log(z)^logpower/(logpower!)
		if (sub[logpower+1]<>[]) and (word[1]=0) then
			result[logpower+1, 0] := result[logpower+1, 0] + sub[logpower+1][1]
		end if:
		# Remaining integrands are (log z)^n/n! * z^m for m>=0 only, so they only lower the log-powers
		for power from 0 to minOrder-1 do
			if word[1]<>0 then
				p := 0:
				for i from 0 to min(power, nops(sub[logpower+1])-1) do
					p := p - sub[logpower+1][i+1]/(word[1])^(power-i+1):
				end do:
			elif (power+1<=nops(sub[logpower+1])-1) then
				p := sub[logpower+1][power+2]:
			else
				p := 0:
			end if:
			# Integrate!
			if p=0 then next: fi:
			p := -p:
			for i from logpower to 0 by -1 do
				p := -p/(power+1):
				result[i, power+1] := result[i, power+1] + p:
				maxpowers[i] := power+1:
			end do:
		end do:
	end do:
	# Remove empty entries
	for logpower from 0 to maxlog do
		while maxpowers[logpower]>=0 do
			if result[logpower, maxpowers[logpower]] = 0 then
				maxpowers[logpower] := maxpowers[logpower] - 1:
			else
				break:
			end if:
		end do:
	end do:
	while maxlog>=0 do
		if maxpowers[maxlog] = -1 then
			maxlog := maxlog-1:
		else
			break:
		end if:
	end:
	[seq([seq(result[logpower, power], power=0..maxpowers[logpower])], logpower=0..maxlog)]:
end proc:

###########################################################################################################################
# Complete integration algorithm for integrals int(f, z=0..infinity)
###########################################################################################################################

# Tests, whether the function is the zero function, by checking reglims and then recursively the derivatives of the function to be zero
testZeroFunction := proc (wordlist::list)
global _hyper_algebraic_roots, _hyper_restrict_singularities, _hyper_allowed_singularities:
local aRoots, rSing, aSing, result:
	# Backup these settings, since they may be modified
	aRoots := _hyper_algebraic_roots:
	rSing, aSing := _hyper_restrict_singularities, _hyper_allowed_singularities:
	# Fibration Basis representation should be zero
	_hyper_algebraic_roots := true:
	result := simplify(fibrationBasis(wordlist, select(var -> op(0,var)<>zeta, [op(indets(wordlist))]))):
	# Restore settings
	_hyper_restrict_singularities, _hyper_allowed_singularities := rSing, aSing:
	_hyper_algebraic_roots := aRoots:
	simplify(eval(result, zeta[2]=Pi^2/6)):
end proc:

integrationStep := proc (wordlist::list, var)
local sub, w, u, tab, polesZero, polesInf, power, logpower, pair, L, counter, startTime, onAxis, positiveLetters:
global _hyper_verbosity, _hyper_abort_on_divergence, _hyper_return_tables, _hyper_divergences, _hyper_verbose_frequency:
	startTime := time():
	if _hyper_verbosity>0 then
		printf("Integrating variable %a from 0 to infinity, integrand has %a terms\n", var, numelems(wordlist)):
	end if:
	# If singularities are restricted, linearFactors depends on the allowed singularities!
	forget(linearFactors):
	forgetExpansions():
	# Create the Lists to hold the pole parts and the result
	polesZero := Array(0.._hyper_max_pole_order, 0.._hyper_max_pole_order, ()->table(sparsereduced)):
	polesInf := Array(0.._hyper_max_pole_order, 0.._hyper_max_pole_order, ()->table(sparsereduced)):
	# Handle each summand (pair of rational function and word list) individually
	counter := 0:
	for pair in wordlist do
		counter := counter + 1:
		if (_hyper_verbosity>1) and (counter mod _hyper_verbose_frequency = 0) then
			printf("  now integrating term %a from %a\n", counter, numelems(wordlist)):
		end if:
		# Transform the integrand to an iterated integral in var and perform the integration
		for sub in transformShuffle(pair[2], var) do
			w := integrate(scalarMul(sub[1], pair[1]), var):
			L := sub[2]:
			expandZeroListInplace(polesZero, L, w, var):
			expandInfListInplace(polesInf, L, w, var):
		end do:
	end do:
	# Report divergences
	if _hyper_verbosity>0 then
		if _hyper_check_divergences then
			printf("checking divergences after integration of %a\n", var):
		else
			WARNING("not checking divergences"):
		end if:
	end if:
	positiveLetters := {}:
	for logpower from 0 to _hyper_max_pole_order do
		for power from 0 to _hyper_max_pole_order do
			# Perform the analytic continuation
			tab := polesInf[logpower,power]:
			for pair in indices(tab, pairs) do
				w, L := selectremove(u -> `or`(op(map(type, u, positive))), lhs(pair)):
				if w=[] then next: fi:
				if numelems(w)>1 then
					error "Integral produced more than one word in product with positive letters: %1", pair:
				end if:
				w := w[1]:
				tab[lhs(pair)] := 0:
				onAxis := select(u->type(u,positive), {op(w)}):
				positiveLetters := positiveLetters union onAxis:
				onAxis := [seq(u=delta[var,u], u in sort([op(onAxis)]))]:
				for sub in breakUpContour([[1, w]], onAxis) do
					u := sort([op(L),op(sub[2])]):
					tab[u] := tab[u] + sub[1]*rhs(pair):
				end do:
			end do:
			# Check for divergences at zero
			if (power = 0 and logpower = 0) then next end if:
			sub := testZeroFunction([seq([rhs(sub), lhs(sub)], sub in indices(polesZero[logpower,power], 'pairs'))]):
			if (sub<>0) then
				_hyper_divergences[var=0, ln(var)^(logpower)/var^(power)] := sub:
				if (_hyper_abort_on_divergence) then
					error "Divergence at %1 of type %2", var=0, ln(var)^(logpower)/var^(power):
				end if:
			end if:
			# Check for divergences at infinity
			sub := testZeroFunction([seq([rhs(sub), lhs(sub)], sub in indices(polesInf[logpower,power], 'pairs'))]):
			if (sub<>0) then
				_hyper_divergences[var=infinity, ln(var)^(logpower)*var^(power)] := sub:
				if (_hyper_abort_on_divergence) then
					error "Divergence at %1 of type %2", var=infinity, ln(var)^(logpower)*var^(power):
				end if:
			end if:
		end do:
	end do:
	if positiveLetters<>{} then
		WARNING("Contour was deformed to avoid potential singularities at %1.", positiveLetters):
	end if:
	# Add the contributions from the limits at infinity and zero (the values in polesZero already have the minus sign in them!)
	for sub in indices(polesZero[0,0], 'nolist') do
		polesInf[0,0][sub] := polesInf[0,0][sub] + polesZero[0,0][sub]:
	end do:
	if _hyper_verbosity>0 then
		printf("finished integration of variable %a in %a seconds, produced %a terms\n", var, time()-startTime, numelems(polesInf[0,0])):
	end if:
	if _hyper_return_tables then
		return eval(polesInf[0,0]):
	else
		return [seq([rhs(sub), lhs(sub)], sub in indices(polesInf[0,0], 'pairs'))]:
	end if:
end proc:

hyperInt := proc (f, vars)
local F, i, var, a, b:
	if not type(vars, list) then
		return hyperInt(f, [vars]):
	elif type(f, list) then
		F := f:
	else
		F := convert(f, HlogRegInf):
	end if:
	for i from 1 to nops(vars) do
		if type(vars[i], equation) then
			var := lhs(vars[i]):
			a, b := op(rhs(vars[i])):
			if a=b then
				return []:
			elif a..b=-infinity..infinity then
				F := [op(eval(F, var = tempIntVar)), op(eval(F, var = -tempIntVar))]:
			elif b=infinity then
				F := eval(F, var=a+tempIntVar):
			elif b=-infinity then
				F := eval(scalarMul(F, -1), var=a-tempIntVar):
			elif a=infinity then
				F := eval(scalarMul(F, -1), var=b+tempIntVar):
			elif a=-infinity then
				F := eval(F, var=b-tempIntVar):
			else
				F := scalarMul(eval(F, var=(a+b*tempIntVar)/(1+tempIntVar)), (b-a)/(1+tempIntVar)^2):
			end if:
			F := integrationStep(F, tempIntVar):
		else
			F := integrationStep(F, vars[i]):
		end if:
	end do:
	F:
end proc:

###########################################################################################################################
# Operations on words: Shuffle-regularization and rational transformations of variables
###########################################################################################################################

reg0 := proc (wordlist::list)
local v, result, w:
	result := table(sparsereduced):
	for w in wordlist do
		for v in regzeroWord(w[2]) do
			result[v[2]] := result[v[2]] + v[1]*w[1]:
		end do:
	end do:
	[seq([normal(rhs(w)),lhs(w)], w in indices(result, 'pairs'))]:
end proc:

regzeroWord := proc (word)
local n, i:
option remember:
	if word = [] then
		return [[1, []]]:
	end if:
	# Count trailing zeros
	n := 0:
	for i from nops(word) by -1 to 1 do
		if word[i] = 0 then
			n := n+1
		else
			break:
		end if:
	end do:
	if n = nops(word) then
		return []:
	end if:
	if n=0 then
		return [[1, word]]:
	end if:
	[seq([i[1], [op(i[2]), word[nops(word)-n]]], i in shuffle([[(-1)^n, [0$n]]], [[1, word[1 .. nops(word)-n-1]]]))]:
end proc:

reginf := proc (wordlist)
local i, result, w, u, v:
option remember:
	result := table(sparsereduced):
	for w in wordlist do
		if w[2]=[] then
			result[[]] := result[[]] + w[1]:
		end if:
		for i from 1 to nops(w[2]) do
			if (w[2][i]=-1) then next: fi:
			for u in shuffle([[(-1)^(i-1), [(-1)$(i-1)]]], [[1, w[2, i+1 .. nops(w[2])]]]) do
				v := [w[2, i], op(u[2])]:
				result[v] := result[v] + w[1]*u[1]:
				v := [-1, op(u[2])]:
				result[v] := result[v] - w[1]*u[1]:
			end do:
		end do:
	end do:
	return [seq([normal(rhs(w)),lhs(w)], w in indices(result, 'pairs'))]:
end proc:

# Replaces leading poles (as shuffles) by substitute-powers
reghead := proc (wordlist::list, letter, substitute := 0)
local n, i, res, w:
	res := []:
	for w in wordlist do
		if nops(w[2]) = 0 then
			res := [op(res), w]:
			next:
		end if:
		n := 0:
		for i from 1 to nops(w[2]) do
			if w[2, i] = letter then
				n := n+1
			else
				break:
			end if:
		end do:
		if n=nops(w[2]) then
			res := [op(res), [w[1]*substitute^n/n!, []]]:
			next:
		end if:
		for i from 0 to n do
			res := [op(res), op(Mul([[(substitute)^(n-i)/(n-i)!, [w[2, n+1]]]], shuffle([[(-1)^i, [letter $ i]]], [[w[1], w[2, n+2 .. nops(w[2])]]])))]:
		end do:
	end do:
	collectWords(res):
end proc:

# Replaces trailing letters by substitute-powers
regtail := proc (wordlist::list, letter, substitute := 0)
local n, i, res, w:
	res := []:
	for w in wordlist do
		if nops(w[2]) = 0 then
			res := [op(res), w]:
			next:
		end if:
		n := 0:
		for i from nops(w[2]) by -1 to 1 do
			if w[2, i] = letter then
				n := n+1
			else
				break:
			end if:
		end do:
		if n=nops(w[2]) then
			res := [op(res), [w[1]*substitute^n/n!, []]]:
			next:
		end if:
		for i from 0 to n do
			res := [op(res), op(Mul(shuffle([[(-1)^i, [letter $ i]]], [[w[1], w[2, 1 .. nops(w[2])-n-1]]]), [[(substitute)^(n-i)/(n-i)!, [w[2, nops(w[2])-n]]]]))]:
		end do:
	end do:
	collectWords(res):
end proc:

# Moebius transform z->z/(z+1) maps in iterated integral from 0 to infinity to a word to be integrated from 0 to 1
convertZeroOne := proc (wordlist::list)
local w, result, i, v:
	result := table(sparsereduced):
	for w in wordlist do
		v := [[w[1], []]]:
		for i to nops(w[2]) do
			if w[2, i] = -1 then
				v := Mul([[1, [0]]], v):
			else
				v := Mul([[1, [0]], [-1, [1/(1+w[2, i])]]], v):
			end if:
		end do:
		for i in v do
			result[i[2]] := result[i[2]] + i[1]:
		end do:
	end do:
	[seq([rhs(w), lhs(w)], w in indices(result, 'pairs'))]:
end proc:

# Implements the transformation z->1/z on the word, transforming int_1^inf to int_1^0; then reverse to int_0^1
convert_1inf_01 := proc (wordlist::list)
local w, result, i, v:
option remember:
	result := table(sparsereduced):
	for w in wordlist do
		v := [[w[1], []]]:
		for i from 1 to nops(w[2]) do
			if w[2, i] = 0 then
#				v := Mul([[1, [0]]], v):
				v := [seq([u[1], [0, op(u[2])]], u in v)]:
			else
#				v := Mul([[1, [0]], [-1, [1/(w[2, i])]]], v):
				v := [seq(op([[u[1], [0, op(u[2])]], [-u[1], [1/w[2, i], op(u[2])]]]), u in v)]:
			end if:
		end do:
		for i in v do
			result[i[2]] := result[i[2]] + i[1]:
		end do:
	end do:
	[seq([rhs(w), lhs(w)], w in indices(result, 'pairs'))]:
end proc:

# Implements the transformation z=(A+B*wz)/(1+w), transforming int_A^B to int_0^infinity
convertABtoZeroInf := proc (wordlist::list, A, B)
local w, result, i, v:
option remember:
	result := table(sparsereduced):
	for w in wordlist do
		v := [[w[1], []]]:
		for i from 1 to nops(w[2]) do
			if w[2][i] = B then
				v := [seq([-u[1], [op(u[2]), -1]], u in v)]:
			else
				v := [seq(op([[-u[1], [op(u[2]), -1]], [u[1], [op(u[2]), (w[2][i]-A)/(B-w[2][i])]]]), u in v)]:
			end if:
		end do:
		for i in v do
			result[i[2]] := result[i[2]] + i[1]:
		end do:
	end do:
	[seq([rhs(w), lhs(w)], w in indices(result, 'pairs'))]:
end proc:

# converts an iterated integral from 0 to 1 into an alternating euler sum (compressed notation like for HPL)
toMZV := proc (wordlist::list)
local result, w, counts, i, poles:
	result := 0:
	for w in wordlist do
		if w[2]=[] then
			result := result + w[1]:
		elif (w[2][1] = 1) or (w[2][-1] = 0) then
			error "Divergent word passed to toMZV()":
		else
			counts := []:
			poles  := []:
			for i from nops(w[2]) to 1 by -1 do
				if w[2][i] = 0 then
					counts[-1] := counts[-1] + 1:
				else
					counts := [op(counts), 1]:
					poles :=  [op(poles), w[2][i]]:
				end if:
			end do:
			poles := [op(poles), 1]:
			result := result + w[1]*(-1)^(nops(counts))*zeta[seq(counts[i]*poles[i+1]/poles[i], i = 1..nops(counts))]:
		end if: 
	end do:
	result:
end proc:

# Wordlist contains pairs [f, [L1,L2,...]] which get multiplied out to [f, L1 shuffle L2 shuffle...]
shuffleCompress := proc (wordlist::list)
local result, w, L, i:
	result := table(sparsereduced):
	for w in wordlist do
		L := [[w[1], []]]:
		for i in w[2] do
			L := shuffle(L, [[1, i]]):
		end do:
		for i in L do
			result[i[2]] := result[i[2]] + i[1]:
		end do:
	end do:
	[seq([rhs(w), lhs(w)], w in indices(result, 'pairs'))]:
end proc:

###########################################################################################################################
# Generation of look-up tables and transformations of periods of the moduli spaces of CP^1 with three and four marked points into MZV and alternating sums
###########################################################################################################################
_zeroInfLookups := table():
_zeroOneLookups := table():

loadPeriods := proc(fileName::string)
global _zeroInfLookups, _zeroOneLookups, _hyper_verbosity, zeroOnePeriods, zeroInfPeriods:
local key:
	if not FileTools[Exists](fileName) then
		error "file \"%1\" not found", fileName:
	end if:
	if _hyper_verbosity>0 then
		printf("Loading periods from %s\n", fileName):
	end if:
	zeroOnePeriods := table():
	zeroInfPeriods := table():
	read fileName:
	for key in indices(zeroOnePeriods) do
		_zeroOneLookups[op(key)] := zeroOnePeriods[op(key)]:
	end do:
	for key in indices(zeroInfPeriods) do
		_zeroInfLookups[op(key)] := zeroInfPeriods[op(key)]:
	end do:
	zeroOnePeriods := table():
	zeroInfPeriods := table():
	gc():
end proc:

if type(_hyper_autoload_periods, 'string') then
	_hyper_autoload_periods := [_hyper_autoload_periods]:
elif not type(_hyper_autoload_periods, 'list'('string')) then
	error "option _hyper_autoload_periods=%1 is not a list of strings", _hyper_autoload_periods:
end if:

for fileName in _hyper_autoload_periods do
	if not FileTools[Exists](fileName) then
		WARNING("file \"%1\" not found", fileName):
	else
		loadPeriods(fileName):
	end if:
end do:

wordsFirst := proc(alphabet::set, letters::integer)
	[alphabet[1]$letters]:
end proc:

wordsNext := proc(alphabet::set, w::list)
local i:
	# w is already the last in lex order:
	if w=[alphabet[numelems(alphabet)]$nops(w)] then
		return false:
	end if:
	# find last letter that is not the last in the alphabet
	i := nops(w):
	while w[i]=alphabet[numelems(alphabet)] do
			i := i-1:
	end do:
	[op(w[1..i-1]),alphabet[1+ListTools[Search](w[i],[op(alphabet)])],alphabet[1]$(nops(w)-i)]:
end proc:

# Generates look-up tables for regulated periods from 0 to 1; supposed to be used to apply a basis reduction afterwards
makeLookups01 := proc(weightMZV::integer, weightAlt::integer)
global _zeroOneLookups:
local w, weight, alphabet, lookups:
	lookups := table():
	# MZV
	alphabet := {1, 0}:
	for weight from 0 to weightMZV do
		w := wordsFirst(alphabet, weight):
		while type(w, 'list') do
			if not assigned(_zeroOneLookups[op(w)]) then
				lookups[op(w)] := zeroOnePeriod(w):
			end if:
			w := wordsNext(alphabet, w):
		end do:
	end do:
	# Euler
	alphabet := {-1, 0, 1}:
	for weight from 0 to weightAlt do
		w := wordsFirst(alphabet, weight):
		while type(w, 'list') do
			if not assigned(_zeroOneLookups[op(w)]) then
				lookups[op(w)] := zeroOnePeriod(w):
			end if:
			w := wordsNext(alphabet, w):
		end do:
	end do:
	# Save those
	save lookups, "todoLookups.m":
end proc:

zeroOnePeriod := proc(w::list)
global _zeroOneLookups:
local v:
	if assigned(_zeroOneLookups[op(w)]) then
		return _zeroOneLookups[op(w)]:
	elif w=[] then
		return 1:
	# Words starting with zero vanish at 1
	elif w[nops(w)] = 0 then
		return add(v[1]*zeroOnePeriod(v[2]), v in reg0([[1,w]])):
	# Regularization of logarithmic divergences at 1
	elif w[1] = 1 then
		return add(v[1]*zeroOnePeriod(v[2]), v in reghead([[1,w]], 1)):
	elif not ({op(w)} subset {-1,0,1}) then
		return Hlog(1, w):
	else
		return toMZV([[1, w]]):
	end if:
end proc:

zeroInfPeriod := proc(w::list)
local scale, a, b, letters:
global _zeroInfLookups:
	if assigned(_zeroInfLookups[op(w)]) then
		return _zeroInfLookups[op(w)]:
	elif w=[] then
		return 1:
	end if:
	letters := {op(w)} minus {0}:
	# Ill-defined constants? Should not occur!
	if `or`(op(map(type, letters, positive))) then
		error "Ill-defined constant occured during integration", Hlog(infinity, [w]):
	# Regularizse at zero to obtain an iterated integral
	elif w[nops(w)]=0 then
		return add(a[1]*zeroInfPeriod(a[2]), a in reg0([[1, w]])):
	# MZV's
	elif letters = {-1} then
		return toMZV(convertZeroOne(reginf([[1, w]]))):
	# MZV's scaled by logarithms
	elif numelems(letters) = 1 then
		scale := -op(letters):
		return zeroInfPeriodRescale(w, scale):
	# Alternating sums, including rescalings
	elif (numelems(letters) = 2) and (letters[1]/letters[2] in {2,1/2,-1}) then
		if letters[1]/letters[2] = 2 then
			scale := -letters[2]:
		else
			scale := -letters[1]:
		end if:
		if scale <> 1 then
			return zeroInfPeriodRescale(w, scale):
		end if:
		# transform {-2,-1,0} to {-1,0,1}
		if not ({op(w)} subset {0, -1, -2}) then
			error "Obtained a period in with %1 not in {0,-1,-2}, should not happen!", {op(w)}:
		end if:
		return add(b[1]*zeroOnePeriod(b[2]), b in convert_1inf_01([[1,[seq(w[a]+1, a=1..nops(w))]]])):
	# Polylogs at roots of unity
	elif {op(map(abs, w))}={1} then
		scale := 0:
		for a from 0 to nops(w) do
			scale := scale + zeroOnePeriod(w[a+1..nops(w)])*add(b[1]*zeroOnePeriod(b[2]), b in convert_1inf_01([[1, w[1..a]]])):
		end do:
		return scale:
	# Anything
	else
		return add(b[1]*zeroOnePeriod(b[2]), b in convertZeroOne(reginf([[1, w]]))):
	end if:
end proc:

zeroInfPeriodRescale := proc(w::list, scale)
local k, result, u, above, below, sub, onAxis:
	if scale=1 then
		error "called with scale=1, should not happen!":
	elif type(-scale, positive) then
		error "called with scale=%1 (lies on cut of ln)":
	else
		result := 0:
		above := {}:
		below := {}:
		u := w:
		for k from 1 to nops(u) do
			u[k] := u[k]/scale:
			if type(u[k], positive) then
				if Im(scale)=0 then
					error "called with %1: Singularity on integration path!", u[k]*scale:
				elif Im(scale)>0 then
					above := above union {u[k]}:
				else
					below := below union {u[k]}:
				end if:
			end if:
		end do:
		onAxis := [seq(k=`if`(k in above, 1, -1), k in sort([op(above union below)]))]:
		for k from 0 to nops(w) do
			if above union below = {} then
				result := result + (-ln(scale))^k/k!*zeroInfPeriod(u[k+1..nops(w)]):
			else
				result := result + add(sub[1]*`*`(op(map(zeroInfPeriod, sub[2]))), sub in breakUpContour([[(-ln(scale))^k/k!, u[k+1..nops(w)]]], onAxis)):
			end if:
		end do:
	end if:
end proc:

###########################################################################################################################
# Projection of a Reginf(w) onto a product of hyperlogarithm algebras
###########################################################################################################################

# Transform a polylogarithm into the basis Hyperlog(vars[1]; singularities(vars[2,...]))*Hyperlog(vars[2]; singularities(vars[3,...]))*...*Hyperlog(vars[n])*Period 
# if projectOnto[var] is set, it is used as a set of allowed polynomials during the transformation into variable var
# prefix = [L1,L2,L3,...] is a list of lists L1=[w1,w2,w3,...], L2=[v1,v2,v3,...], and so on telling that we have to multiply with sum_i,j Hlog(var1, w_i)*Hlog(var2, v_j) and so on...
# Note that each w_i = [lambda_i, word_i] is a pair of coefficient and actual word!
# Transform a polylogarithm into the basis Hyperlog(vars[1]; singularities(vars[2,...]))*Hyperlog(vars[2]; singularities(vars[3,...]))*...*Hyperlog(vars[n])*Period 
# if projectOnto[var] is set, it is used as a set of allowed polynomials during the transformation into variable var
fibrationBasis := proc(wordlist, vars::list := [], store := false, projectOnto::table := table(), prefix::list := [], valueFactor := 1)
local result, w, pair, val, i, counter, sizes, prefixes, key:
global _hyper_restrict_singularities, _hyper_allowed_singularities:
	if not type(wordlist, list) then
		return fibrationBasis(convert(wordlist, `HlogRegInf`), _passed[2.._npassed]):
	elif type(store, table) then
		result := store:
	else
		result := table(sparsereduced):
	end if:
	if nops(vars)=0 then
		val := add(w[1]*mul(zeroInfPeriod(u), u in w[2]), w in wordlist)*valueFactor:
		# unfold the cartesian product of prefix-lists
		sizes := map(numelems, prefix):
		prefixes := numelems(prefix):
		counter := [1$prefixes]:
		do
			key := [seq(prefix[i][counter[i]][2], i = 1..prefixes)]:
			result[key] := result[key] + val*mul(prefix[i][counter[i]][1], i = 1..prefixes):
			# Increment counters
			i := 1:
			while i<=prefixes do
				if counter[i]=sizes[i] then
					counter[i] := 1:
					i := i+1:
				else
					counter[i] := counter[i]+1:
					break:
				end if:
			end do:
			if i>prefixes then
				break:
			end if:
		end do:
	else
		for w in wordlist do
			_hyper_restrict_singularities := assigned(projectOnto[vars[1]]):
			_hyper_allowed_singularities := projectOnto[vars[1]]:
			for pair in transformShuffle(w[2], vars[1]) do
				fibrationBasis(pair[2], vars[2..nops(vars)], result, projectOnto, [op(prefix),pair[1]], valueFactor*w[1]):
			end do:
		end do:
	end if:
	# Return result in readable form
	if not type(store, table) then
		return add(result[w]*mul(`if`(w[i]=[], 1, Hlog(vars[i], w[i])), i=1..nops(vars)), w in indices(result, nolist)):
	end if:
end proc:

# Takes a fibration basis representation and shuffles every factor with the corresponding word in the second argument list
fibrationBasisProduct := proc(expr::table, shuffleIn::list, result::table, multiplier:=1)
local L, shuffled, i, dim, sizes, counter, key, val:
	dim := numelems(shuffleIn):
	shuffled := table():
	for L in indices(expr, 'nolist') do
		val := expr[L]:
		for i from 1 to dim do
			shuffled[i] := shuffleWords(L[i], shuffleIn[i]):
		end do:
		# unfold the cartesian product of prefix-lists
		sizes := map(numelems, shuffled):
		counter := [1$dim]:
		do
			key := [seq(shuffled[i][counter[i]], i = 1..dim)]:
			result[key] := result[key] + val*multiplier:
			# Increment counters
			i := 1:
			while i<=dim do
				if counter[i]=sizes[i] then
					counter[i] := 1:
					i := i+1:
				else
					counter[i] := counter[i]+1:
					break:
				end if:
			end do:
			if i>dim then
				break:
			end if:
		end do:
	end do:
end proc:

# Takes a fibrationBasis representation, integrates the first variable in the fibration sequence; produces a result in the fibre-Basis
fibreIntegration := proc(expr::table, vars, result::table, projectOnto::table := table())
global _hyper_verbosity, _hyper_verbose_frequency, _hyper_max_pole_order, _hyper_restrict_singularities, _hyper_allowed_singularities:
local L, counter, fibreLog, primitive, poles:
	poles := Array(0.._hyper_max_pole_order, 0.._hyper_max_pole_order, ()->table(sparsereduced)):
	if numelems(result)>0 then
		printf("Warning: Result table already has contents!\n"):
	end if:
	counter := 0:
	for L in indices(expr, 'nolist') do
		if (_hyper_verbosity>1) and (counter mod _hyper_verbose_frequency = 0) then
			printf("Integrated %a out of %a, result has %a terms\n", counter, numelems(expr), numelems(result)):
		end if:
		counter := counter + 1:
		# Integrate the hyperlog depending on var[1] from 0 to infinity
		# then express the result in the fibration basis along [vars[2], ...]
		_hyper_restrict_singularities := assigned(projectOnto[vars[1]]):
		_hyper_allowed_singularities := projectOnto[vars[1]]:
		primitive := integrate([[expr[L], L[1]]], vars[1]):
		poles[0,0] := table(sparsereduced):
		expandZeroListInplace(poles, [[1,[]]], primitive, vars[1]):
		expandInfListInplace(poles, [[1,[]]], primitive, vars[1]):
		primitive := [seq([rhs(w), lhs(w)], w in indices(poles[0,0], 'pairs'))]:
		# Replace ones from the integration!
#		primitive := [seq([rhs(w), map2(map, zero->`if`(zero=1,1+epsilon,zero), lhs(w))], w in indices(poles[0,0], 'pairs'))]:
		if 1 in {seq(op(map(op, w[2])), w in primitive)} then
			if _hyper_verbosity>10 then
				printf("Breaking up contour at 1\n"):
			end if:
			primitive:=shuffleCompress(primitive):
			primitive := breakUpContour(primitive, [1=delta[vars,1]]):
		end if:
		fibreLog := table(sparsereduced):
		fibrationBasis(primitive, vars[2..nops(vars)], fibreLog, projectOnto):
		if (_hyper_verbosity>1) and (counter mod _hyper_verbose_frequency = 0) then
			printf("  Integral of fibre form has %a terms (before basis projection: %a terms)\n", numelems(fibreLog), numelems(primitive)):
		end if:
		# Shuffle everything together and add to the final result
		fibrationBasisProduct(fibreLog, L[2..nops(vars)], result):
	end do:
end proc:

# Assumes trivial integration step (no partial integrations); i.e. no expansion at zero and infinity necessary
# Here, expr is a table([word=list]), where word is the hyperlog in vars[1] to be integrated, and the list=[[f1,L2,...,Ln], [...], ...] where n=nops(vars) gives the factors f1*Hlog(vars[2],L2)*...*Hlog(vars[n],Ln) that multiply Hlog(vars[1], word)
# This avoids multiple integration of the same Hlog(vars[1], word)
# prefactor is the overall rational prefactor, i.e. 1/denominator
fibreIntegrationSimple := proc(expr::table, vars, prefactor::ratpoly, result::table, projectOnto::table := table())
global _hyper_verbosity, _hyper_verbose_frequency, _hyper_restrict_singularities, _hyper_allowed_singularities:
local L, counter, fibreLog, primitive:
	if numelems(result)>0 then
		printf("Warning: Result table already has contents!\n"):
	end if:
	counter := 0:
	for L in indices(expr, 'nolist') do
		counter := counter + 1:
		if (_hyper_verbosity>1) and (counter mod _hyper_verbose_frequency = 0) then
			printf("Integrated %a out of %a, result has %a terms\nNow considering Hlog(%a, %a)\n", counter, numelems(expr), numelems(result), vars[1], L):
		end if:
		# Integrate the hyperlog depending on var[1] from 0 to infinity
		_hyper_restrict_singularities := assigned(projectOnto[vars[1]]):
		_hyper_allowed_singularities := projectOnto[vars[1]]:
		primitive := integrate([[prefactor, L]], vars[1]):
		primitive := reg0(primitive):
		# Transform to shuffle-representation as expected input format of fibrationBasis
		primitive := map(w->[w[1],[w[2]]], primitive):
		# express the result in the fibration basis along [vars[2], ...]
		fibreLog := table(sparsereduced):
		fibrationBasis(primitive, vars[2..nops(vars)], fibreLog, projectOnto):
		if (_hyper_verbosity>1) and (counter mod _hyper_verbose_frequency = 0) then
			printf("  Integral of fibre form has %a terms (before basis projection: %a terms)\nNow shuffling in %a multipliers\n", numelems(fibreLog), numelems(primitive), numelems(expr[L])):
		end if:
		# Shuffle everything together and add to the final result
		for primitive in expr[L] do
			if (_hyper_verbosity>1) and (counter mod _hyper_verbose_frequency = 0) then
				printf("-Now shuffling in:\n"):
				print(primitive):
			end if:
			fibrationBasisProduct(fibreLog, primitive[2..nops(vars)], result, primitive[1]):
		end do:
	end do:
end proc:

##############################################################################################################################
# Convenience routines for Maple-integration and treatment of individual hyperlogarithms (not used by integration algorithm)
##############################################################################################################################

`diff/Hlog` := proc(arg, word::list, var)
local result, i, f:
	if word=[] then
		return 0:
	end if:
	# differential w.r.t. upper boundary:
	result := diff(arg, var)/(arg-word[1])*Hlog(arg, word[2..nops(word)]):
	# difference of two neighbouring zeros
	for i from 1 to nops(word)-1 do
		f := word[i]-word[i+1]:
		if simplify(f)=0 then
			next:
		end if:
		result := result + diff(ln(f), var)*(Hlog(arg, subsop(i+1=NULL, word))-Hlog(arg, subsop(i=NULL, word))):
	end do:
	# last letter
	f := word[nops(word)]:
	if f<>0 then
		result := result - diff(ln(f), var)*Hlog(arg, word[1..nops(word)-1]):
	end if:
	# first letter
	if arg<>infinity then
		result := result - diff(word[1], var)/(arg - word[1])*Hlog(arg, word[2..nops(word)]):
	end if:
	return result:
end proc:

`diff/Mpl` := proc(ns::list, zs::list, var)
local j, result, inner, sub:
	result := 0:
	for j from 1 to nops(ns) do
		inner := diff(zs[j], var):
		if inner = 0 then next: end if:
		if ns[j]>1 then
			sub := Mpl(subsop(j=ns[j]-1, ns), zs)/zs[j]:
		elif ns[j]<>1 then
			error "Only Mpl with all indices positive integers supported":
		elif ns=[1] then
			sub := 1/(1-zs[1]):
		elif j=nops(ns) then
			sub := Mpl(subsop(j=NULL, ns), subsop(j-1=zs[j-1]*zs[j], j=NULL, zs))/(1-zs[j]):
		elif j=1 then
			sub := Mpl(subsop(j=NULL, ns), subsop(j=NULL, j+1=zs[j]*zs[j+1], zs))/(zs[j]*(zs[j]-1))-Mpl(subsop(j=NULL, ns), subsop(j=NULL, zs))/(zs[j]-1):
		else
			sub := Mpl(subsop(j=NULL, ns), subsop(j=NULL, j+1=zs[j]*zs[j+1], zs))/(zs[j]*(zs[j]-1))-Mpl(subsop(j=NULL, ns), subsop(j-1=zs[j-1]*zs[j], j=NULL, zs))/(zs[j]-1):
		end:
		result := result + inner*sub:
	end do:
	result:
end proc:

MplSum := proc(ns::list, zs::list, N)
local subns, subzs, k, n:
	if ns=[] then
		1:
	else
		n := nops(ns):
		subns := subsop(n=NULL, ns):
		subzs := subsop(n=NULL, zs):
		add(MplSum(subns, subzs, k-1)*zs[n]^k/k^ns[n], k=1..N):
	end if:
end proc:

`series/Mpl` := proc(ns::list, zs::list, _at)
local j, at:
	if type(_at, equation) then
		at := _at:
	else
		at := _at=0:
	end if:
	if not (lhs(at) in indets(zs)) then
		return Mpl(ns, zs):
	end if:
	if limit(zs[nops(ns)], at)<>0 then
		error "Only expansion for last argument close to zero implemented":
	end if:
	for j from 1 to nops(ns) do
		if type(limit(zs[j], at), Or(infinity,undefined)) then
			return undefined:
		end if:
	end do:
	series(MplSum(ns, zs, Order) + O(zs[nops(ns)]^(Order+1)), at):
end proc:

`series/Hlog` := proc (arg, word::list, at)
local result, expa, n, m:
	if type(at, equation) then
		if (lhs(at)<>arg) or (rhs(at)<>0) then
			error "Only expansion %1 -> 0 implemented", arg:
		end if:
	elif at<>arg then
		error "Only expansion %1 -> 0 implemented", arg:
	end if:
	expa := zeroExpansion(word, Order):
	result := 0:
	for n to nops(expa) do
		for m to nops(expa[n]) do
			result := result + expa[n][m]*ln(arg)^(n-1)*arg^(m-1)/(n-1)!:
		end do:
	end do:
	series(result + O(arg^(Order+1)), arg):
end proc:

# Does not attempt any simplification in advance
findDenominators := proc(expr)
	if type(expr, 'list') then
		`union`(seq(
			{op(map2(op, 1, factors(denom(word[1]))[2]))},
			word in expr
		)):
	elif op(0,expr) in {`+`, `*`} then
		`union`(op(map(findDenominators, [op(expr)]))):
	elif op(0,expr) <> `^` then
		{}:
	elif op(2,expr)>0 then
		findDenominators(op(1,expr)):
	else
		{op(map2(op, 1, factors(op(1,expr))[2]))}:
	end if:
end proc:

# Extract the letters that appear in the words of an Hlog-Representation
findLetters := proc(expr, asPolynom::boolean:=false)
local var, letter, term, result:
	if type(expr, 'list') then
		return factor({op(map(op,map(term -> op(term[2]),expr)))}):
	end if:
	# Assume fibrationBasis-representation and collect letters for each variable
	result := table():
	for term in indets(expr, 'specfunc(anything,Hlog)') do
		if op(0, term)<>Hlog then
			next:
		end if:
		var := op(1, term):
		letter := factor({op(op(2,term))}):
		if not assigned(result[var]) then
			result[var] := letter:
		else
			result[var] := result[var] union letter:
		end if:
	end do:
	if asPolynom then
		for var in indices(result,nolist) do
			result[var] := select(term->degree(term, var)>0, irreducibles(result)) union `if`(0 in result[var], {var}, {}):
		end do:
	end if:
	return eval(result):
end proc:

# Explicitly enforces the shuffle-Regularistation such that only Hlog's holomorphic at zero survive
`value/Hlog` := proc(var, word::list)
	add(w[1]*`if`(w[2]=[], 1, Hlog(var,w[2])), w in regtail([[1,word]], 0, ln(var))):
end proc:

HlogAsMpl := proc(var, word::list)
local r, i, sigma, nu:
	if word=[] then
		return 1:
	elif word[nops(word)] = 0 then
		return add(nu[1]*HlogAsMpl(var, nu[2]), nu in regtail([[1, word]], 0, ln(var))):
	end if:
	i:=nops(word):
	sigma := []:
	nu := []:
	r := 0:
	while i>=1 do
		r := r+1:
		sigma := [op(sigma), word[i]]:
		nu := [op(nu), 1]:
		i := i-1:
		while i>=1 do
			if word[i]<>0 then
				break:
			end if:
			nu[r] := nu[r] + 1:
			i := i-1:
		end do:
	end do:
	return (-1)^r*Mpl(nu, [seq(sigma[i+1]/sigma[i], i=1..r-1), var/sigma[r]]):
end proc:

MplAsHlog := proc(ns::list, zs::list)
	(-1)^(nops(ns))*Hlog(1, [seq(op([0$(ns[-i]-1), 1/mul(zs[j], j=-i..-1)]), i=1..nops(ns))]):
end proc:

`convert/Hlog` := proc(expr)
	eval(eval(expr, [polylog=((n,var)->Mpl([n],[var])), dilog=(var->Mpl([2], [1-var]))]), [ln = (var->Hlog(var, [0])), Mpl = MplAsHlog, Hpl=HplAsHlog]):
end proc:

(*
`print/Hlog` := proc(var, word::list)
	Hlog[op(word)](var):
end proc:

`print/Mpl` := proc(ns::list, zs::list)
	# Suppress 1's for MPLs of a single argument
	if zs = [1$(nops(zs)-1), zs[-1]] then
		`Mpl`[op(ns)](zs[-1]):
	else
		`Mpl`[op(ns)](op(zs)):
	end if:
end proc:

`latex/Hlog` := proc(var, word::list)
	cat("\\L_{", op(ListTools[Join](map(cat@`latex/print`, word), ",")), "}\\left(", `latex/print`(var), "\\right)"):
end proc:

`latex/Mpl` := proc(ns::list, zs::list)
	cat("\\Li_{", op(ListTools[Join](map(cat@`latex/print`, ns), ",")), "}\\left(", op(ListTools[Join](map(cat@`latex/print`, zs), ",")), "\\right)"):
end proc:
*)

`latex/Hlog` := proc(var, word::list)
	cat("\\Hlog{", `latex/print`(var), "}{", op(ListTools[Join](map(cat@`latex/print`, word), ",")), "}"):
end proc:

`latex/Mpl` := proc(ns::list, zs::list)
	cat("\\Mpl{", op(ListTools[Join](map(cat@`latex/print`, ns), ",")), "}{", op(ListTools[Join](map(cat@`latex/print`, zs), ",")), "}"):
end proc:


`convert/Mpl` := proc(expr)
	eval(eval(expr, Hpl=HplAsHlog), [polylog=((n,var)->Mpl([n],[var])), dilog=(var->Mpl([2], [1-var])), Hlog = HlogAsMpl]):
end proc:

HplAsHlog := proc(var, word::list)
	if word=[] then
		return 1:
	end if:
	(-1)^(nops(select(w->w>0, word)))*Hlog(var, [seq(`if`(w=0, 0, op([0$(abs(w)-1), signum(w)])), w in word)]):
end proc:

HlogAsHpl := proc(var, word::list)
local ns, i, had, prefac:
	if word=[] then
		return 1:
	# Check if word is a Hpl
	elif not ({op(word)} subset {-1,0,1}) then
		return Hlog(var, word):
	end if:
	had := false:
	ns := []:
	prefac := 1:
	for i from nops(word) to 1 by -1 do
		if (word[i] = 0) and had then
			ns[1] := signum(ns[1])*(abs(ns[1])+1):
		else
			ns := [word[i], op(ns)]:
			if word[i]<>0 then
				had := true:
			end if:
			if word[i] = 1 then
				prefac := prefac*(-1):
			end if:
		end if:
	end do:
	prefac*Hpl(var, ns):
end proc:

`convert/Hpl` := proc(expr)
	eval(expr, [Hlog=HlogAsHpl, polylog = ((n,var)->Hpl(var,[n])), dilog = (var->Hpl(1-var, [2])), ln = (var->Hpl(var, [0]))]):
end proc:

# Convert iterated integrals Hlog(var, word) into integrals from 0 to 1: i[0, ..., 1]
# suitable for numeric evaluation with zeta_procedures
`convert/i` := proc(expr)
	eval(convert(expr, Hlog), Hlog=HlogAsi):
end proc:

HlogAsi := proc(var, word::list)
	add(w[1]*`if`(w[2]=[], 1, i[0,seq(r/var, r in ListTools[Reverse](w[2])), 1]), w in regtail([[1,word]], 0, ln(var))):
end proc:

# Conver Hlog(var, word) into internal representation as integrals from 0 to infinity
`convert/HlogRegInf` := proc(expr)
local result, i, var, word:
	if type(expr, list) then
		error "List supplied. Probably already in the format HlogRegInf?":
	elif op(0,expr)=`+` then
		return collectWords([seq(op(`convert/HlogRegInf`(op(i, expr))), i=1..nops(expr))]):
	elif op(0,expr)=`*` then
		result := [[1,[]]]:
		for i from 1 to nops(expr) do
			result := shuffleSymbolic(result, `convert/HlogRegInf`(op(i, expr))):
		end do:
		return result:
	elif op(0,expr)=`Hlog` then
		var := op(1, expr):
		word := op(2, expr):
		if word=[] then
			return [[1, []]]:
		end if:
		# Word ends in nonzero letter, so we have an iterated integral and can transform the variables inside the integral, z=1/(w+1), w=1/z-1
		if word[nops(word)] <> 0 then
			result := [[1, []]]:
			for i from 1 to nops(word) do
				if word[i]=0 then
					result := Mul([[1, [-1]]], result)
				else
					result := Mul([[1, [-1]], [-1, [var/word[i]-1]]], result):
				end if:
			end do:
			return [seq([w[1], [w[2]]], w in result)]:
		end if:
		# Powers of logs
		if word = [0$nops(word)] then
			return [[(-1)^nops(word)/(nops(word)!), [[-var]$nops(word)]]]:
		end if:
		# enforce shuffle regularization: products of log-powers and iterated integrals
		return `convert/HlogRegInf`(add(w[1]*Hlog(var, w[2]), w in regtail([[1,word]], 0, Hlog(var, [0])))):
	# Plain logs
	elif op(0,expr) = `ln` then
		return `convert/HlogRegInf`(Hlog(op(expr), [0])):
	# Classical polylogarithms
	elif op(0,expr) = `polylog` then
		return `convert/HlogRegInf`(Mpl([op(1, expr)], [op(2,expr)])):
	elif op(0,expr) = `dilog` then
		return `convert/HlogRegInf`(Mpl([2], [1-op(1,expr)])):
	# Harmonic polylogarithms
	elif op(0,expr) = `Hpl` then
		return `convert/HlogRegInf`(HplAsHlog(op(expr))):
	# Multiple polylogarithms
	elif op(0,expr) = `Mpl` then
		return `convert/HlogRegInf`(`convert/Hlog`(expr)):
	# in Powers like (Hlog(z, ...))^2, we need to expand the base and multiply...
	elif op(0,expr)=`^` then
		i := op(2,expr):
		if type(i, integer) and (i>0) then
			result := [[1,[]]]:
			word := `convert/HlogRegInf`(op(1,expr)):
			for var from 1 to i do
				result := shuffleSymbolic(result, word):
			end do:
			return result:
		end if:
	end if:
	# Otherwise we have some constant:
	[[expr,[]]]:
end proc:

########################################################################################
# Utilities for Feynman graphs and Feynman integrals
########################################################################################

laplaceMatrix := proc (edges)
local M, n, e, i, j:
	n := max({seq(max(e), e in edges)}):
	M := Matrix(1..n, 1..n):
	for e from 1 to nops(edges) do
		i := edges[e][1]:
		j := edges[e][2]:
		M[i, i] := M[i, i] + x[e]:
		M[j, j] := M[j, j] + x[e]:
		M[i, j] := M[i, j] - x[e]:
		M[j, i] := M[j, i] - x[e]:
	end do:
	M:
end proc:

graphPolynomial := proc (edges)
uses LinearAlgebra:
local M, n:
	M := laplaceMatrix(edges):
	n := RowDimension(M):
	expand(mul(x[e], e=1..nops(edges))*subs([seq(x[e]=1/x[e], e=1..nops(edges))], Determinant(M[2..n,2..n]))):
end:

forestPolynomialRecursive := proc(edges::list, nextEdge, par, parGoal)
local result, S, V, e:
	if numelems(par)=numelems(parGoal) then
		# Check if each component contains one of parGoal (redundant if implementation is correct)
		for V in par do
			if numelems(select(P->P subset V, parGoal))<>1 then
				error "This should not happen!":
			end if:
		end do:
		return mul(x[e], e=nextEdge..numelems(edges)):
	end if:
	if numelems(par)<=numelems(parGoal) then #(redundant check if everything is correct)
		error "This should not happen as par should always be compatible with parGoal and thus here only bigger!":
	end if:
	# Not enough edges left?
	if numelems(par)-numelems(parGoal)>numelems(edges)-nextEdge+1 then
		return 0:
	end if:
	# Take the next edge
	V := {op(edges[nextEdge])}:
	S := select(P->(P intersect V <> {}), par):
	if (numelems(S)=2) and (numelems(select(P->(P intersect (S[1] union S[2]) <> {}), parGoal))<=1) then
		result := forestPolynomialRecursive(edges, nextEdge+1, (par minus S) union {S[1] union S[2]}, parGoal):
	else
		result := 0:
	end if:
	# Do not take the next edge
	result + x[nextEdge]*forestPolynomialRecursive(edges, nextEdge+1, par, parGoal):
end proc:

# Spanning forest polynomial as defined by Karen Yeats; Par is a partition of a subset of vertices
forestPolynomial := proc(edges::list, Par::set)
	forestPolynomialRecursive(edges, 1, {seq({v}, v in {op(map(op, edges))})}, Par):
end proc:

# Externals contains pairs (v, var) of a vertex v and its incoming momentum squared var
# If supplied, masses is a list of the masses of all internal lines
secondPolynomial := proc(edges::list, externals::list, masses::list := [])
local phi, e, v, V:
	# Vertices with external momenta attached:
	V := {op(map2(op, 1, externals))}:
	# add two-forests isolating one momentum
	if numelems(V)=2 then
		if externals[1][2]<>externals[2][2] then
			error "Only one external momentum; has to be the same! But %1 is not %2!", externals[1][2], externals[2][2]:
		else
			phi := externals[1][2]*forestPolynomial(edges, {{externals[1][1]}, {externals[2][1]}}):
		end if:
	else
		phi := add(v[2]*forestPolynomial(edges, {{v[1]}, V minus {v[1]}}), v in externals):
	end if:
	# add Mandelstams
	if numelems(externals)=4 then
		phi := phi + s*forestPolynomial(edges, {{externals[1][1], externals[2][1]}, {externals[3][1], externals[4][1]}}):
		phi := phi + t*forestPolynomial(edges, {{externals[1][1], externals[3][1]}, {externals[2][1], externals[4][1]}}):
		phi := phi + u*forestPolynomial(edges, {{externals[1][1], externals[4][1]}, {externals[2][1], externals[3][1]}}):
	end if:
	if numelems(externals)>4 then
		# we index the momentum squares by the sets of vertices containing 1
		for v from 1 to nops(V)-3 do
			phi := phi + add(s[e union {V[1]}]*forestPolynomial(edges, {e union {V[1]}, V minus (e union {V[1]})}), e in combinat[choose](V minus {V[1]},v)):
		end do:
	end if:
	# add Masses
	if masses<>[] then
		if numelems(masses)<>numelems(edges) then
			error "Masses not given for all edges!":
		end if:
		phi := phi + graphPolynomial(edges)*add(masses[e]*x[e], e=1..numelems(edges)):
	end if:
	# return
	phi:
end proc:

# parametric Integrand for a graphical Function
# edges contains two-sets for propagators and lists for inverse propagators
# externals is [vz,v0,v1,vinf] or [vz,v0,v1]
graphicalFunction := proc(edges::list, externals::list)
local nodes, numers, e, integ, v0, v1, vz, L, phi, psi, v, w, k, iNode, internals, A, E, sdd:
	nodes := {op(map(op,edges))}:
	if nops(externals)=4 then
		nodes := nodes minus {externals[4]}:
	end if:
	for v from 1 to nops(nodes) do
		iNode[nodes[v]] := v:
	end do:
	numers := {}:
	integ := 1:
	vz,v0,v1 := op(1..3, externals):
	E := 0:
	for k from 1 to nops(edges) do
		e := edges[k]:
		# Remove infinity
		if nops(externals)=4 then
			if externals[4] in {op(e)} then
				next:
			end if:
		end if:
		# Remove edges between external vertices
		if {op(e)} subset {op(externals)} then
			if e = {v0,vz} then
				integ := integ/z/zz:
			elif e = {v1,vz} then
				integ := integ/(1-z)/(1-zz):
			elif {op(e)} = {v0,vz} then
				integ := integ*z*zz:
			elif {op(e)} = {v1,vz} then
				integ := integ*(1-z)*(1-zz):
			end if:
			next:
		end if:
		E := E + 1:
		if e <> {op(e)} then
			numers := numers union {k}:
		end if:
	end do:
	# Laplace Matrix
	internals := nodes minus {op(externals)}:
	L := Matrix(1..nops(nodes), 1..nops(nodes)):
	for k from 1 to nops(edges) do
		e := {op(edges[k])}:
		if (not e subset nodes) or (e intersect internals = {}) then
			next:
		end if:
		v := iNode[e[1]]:
		w := iNode[e[2]]:
		L[v,w] := L[v,w] - x[k]:
		L[w,v] := L[w,v] - x[k]:
		L[v,v] := L[v,v] + x[k]:
		L[w,w] := L[w,w] + x[k]:
	end do:
	# Polynomials
	A:=[op({seq(iNode[v], v in internals)})]:
	psi := LinearAlgebra[Determinant](L[A,A]):
	phi := -LinearAlgebra[Determinant](L[[op(A),iNode[v0]],[op(A),iNode[v1]]]):
	phi := phi - z*zz*LinearAlgebra[Determinant](L[[op(A), iNode[v0]],[op(A), iNode[vz]]]):
	phi := phi - (1-z)*(1-zz)*LinearAlgebra[Determinant](L[[op(A),iNode[v1]],[op(A), iNode[vz]]]):
	# integrate out the variables for inverse propagators by partial integration
	integ := integ/psi^2:
	for k in numers do
		# Rational prefactor:
		integ := limit(-diff(integ, x[k]) + integ*diff(phi/psi, x[k]), x[k]=0):
		# Exponent still present?
		if phi=0 then
			next:
		end if:
		# Take limit x[k]->0 in exponent phi/psi
		if eval(psi, x[k]=0)<>0 then
			psi := eval(psi, x[k]=0):
			phi := eval(phi, x[k]=0):
		elif eval(phi, x[k]=0)<>0 then
			# This means exp(-1/x[k]), killing everything rational
			return 0:
		else
			psi := diff(psi, x[k]):
			phi := diff(phi, x[k]):
		end if:
	end do:
	# No integrations left?
	if E=nops(numers) then
		return integ:
	end:
	# Still integrations to do; transform to projective integral
	if phi=0 then
		return infinity:
	end if:
	A := subs([seq(x[k]=t*x[k], k=1..nops(edges))], integ)*t^(E-nops(numers)):
	A := convert(A, 'polynom', t):
	integ := 0:
	if ldegree(A,t)<=0 then
		return infinity:
	end if:
	for sdd from ldegree(A,t) to degree(A,t) do
		integ := integ + coeff(A, t, sdd)*(phi/psi)^(-sdd)*GAMMA(sdd):
	end do:
	return integ:
end proc:

drawGraph := proc(edges::list, momenta::list := [], masses::list := [], drawStyle := planar)
local G, e, v, S:
uses GraphTheory:
	G:=Graph({seq([{op(edges[e])}, e], e=1..nops(edges))}):
	# Vertices with null external momenta:
	S := {seq(`if`(v[2]=0, v[1], NULL), v in momenta)}:
	if numelems(S)>0 then
		HighlightVertex(G, S, green):
	end if:
	# Vertices with massive external momenta:
	S := {seq(`if`(v[2]=0, NULL, v[1]), v in momenta)}:
	if numelems(S)>0 then
		HighlightVertex(G, S, magenta):
	end if:
	# Massive edges and inverse propagators:
	if masses<>[] then
		S := remove(e->masses[e]=0, {seq(e, e=1..nops(masses))}):
	else
		S := select(e->edges[e]=[op(edges[e])], {seq(e, e=1..nops(edges))}):
	end if:
	S := map(e->{op(edges[e])}, S):
	if numelems(S)>0 then
		HighlightEdges(G, S):
	end if:
	# Draw the graph:
	if (drawStyle=planar) and (IsPlanar(G)) then
		DrawGraph(G, style=planar):
	elif drawStyle=planar then
		DrawGraph(G, style=spring):
	else
		DrawGraph(G, style=drawStyle):
	end if:
end proc:

########################################################################################
# Polynomial reduction
########################################################################################

# Uses remember for better runtime
myfactors := proc(f, bound:=false)
global _hyper_use_factor_bounds, _hyper_splitting_field:
option cache:
	if (bound=false) or (not _hyper_use_factor_bounds) then
		if bound = false then
			return [seq(i[1], i in op(2, factors(f, _hyper_splitting_field)))]:
		else
			return [op({seq(i[1], i in op(2, factors(f, _hyper_splitting_field)))} intersect bound)]:
		end if:
	else
		return [seq(`if`(divide(f, q), q, NULL), q in bound)]:
	end if:
end proc:

# For polynomial reduction: factors polynomials in set and discards any constants and monomials except those in 'parameters'
# if bound is given, the result is intersected with bound; effectively factors only looks for divisors in bound
irreducibles := proc (X::set, parameters::set := {}, bound := false)
local result, f, i:
	result := {}:
	for f in X minus {0} do
		for i in myfactors(f, bound) do
			# Drop monomials
			if {i}<>indets(i) then
				result := result union {i}:
			elif i in parameters then
				result := result union {i}:
			end if:
		end do:
	end do:
	result:
end proc:

# Returns the set of variables that all polynomials are (at worst) linear in
findLinearVariables := proc(polys::set)
	select(var -> max(map(degree, polys, var))<=1, indets(polys)):
end proc:

# L is the polynomial reduction, result is the set of possible singularities in the Hyperlogarithm-Algorithm-Output
# vars is the order of integration
# returns false if at some stage a non-linear polynomial is detected
findHyperlogPoles := proc(L::table, vars::list)
local result, integrated, polys, p, var, zeros, leaders, temp:
	result := {}:
	for integrated from 1 to numelems(vars) do
		var := vars[integrated]:
		# Take limit of singularities already present and separate different vanishing degrees
		result := map(op@leadCoeffs, result, var):
		result := map(f-> f minus {0}, result):
		# Add singularities from transformation into a hyperlog in the variable vars[integrated]
		zeros := {}:
		polys := L[{op(vars[1..integrated-1])}]:
		# Compatibility graph? Then only take its vertices
		if type (polys, 'list') then
			polys := polys[1]:
		end if:
		for p in polys do
			if degree(p, var)>1 then
				error "nonlinear polynomial in %a: %a", var, p:
			end if:
			if degree(p, var)=0 then
				next:
			end if:
			zeros := zeros union {normal(-coeff(p, var, 0)/coeff(p, var, 1))}:
		end do:
		result := result union {zeros}:
	end do:
	map(p->p union {0}, result):
end proc:

# For the set vars of variables, consider all permutations that are linearly reducible and keep those whose Pole sets are minimal w.r.t. inclusion
# Returns a list [(S,P),...] with the minimal pole set S and the corresponding permutations P={p1,...}
# Note that orderings of vars that are linearly reducible but whose poles S are not minimal (i.e. there exists another ordering with strictly smaller pole set) are not listed!
minimalPoleSets := proc(L::table, vars::set)
local result, ordering, S, M:
	result := table():
	for ordering in combinat[permute]([op(vars)]) do
		S := findHyperlogPoles(L, ordering):
		if S=false then
			next:
		end if:
		# If S equals some minimal set already found, add the permutation
		if S in {indices(result, 'nolist')} then
			result[S] := result[S] union {ordering}:
			next:
		end if:
		for M in indices(result, 'nolist') do
			if M subset S then
				# S is not minimal
				S := false:
				break:
			end if:
			if S subset M then
				# M is not minimal
				unassign('result[M]'):
			end if:
		end do:
		# Add S if it is a new minimal set
		if S<>false then
			result[S] := {ordering}:
		end if:
	end do:
	[seq([S, result[S]], S in indices(result, 'nolist'))]:
end proc:

# Finds the variable sets with fewest polynomials in the reduction
reductionInfo := proc(L::table)
local S, best, counts, n:
	S := {indices(L, 'nolist')}:
	S := select(n->L[n][1]<>{}, S):
	best := [seq(select(f->numelems(f)=n, S), n=1..nops(S[-1]))]:
	counts := map(M->min(map(w->numelems(L[w][1]), M)), best):
	best := [seq(select(w->numelems(L[w][1])=counts[n], best[n]), n=1..nops(best))]:
	for n from 1 to nops(best) do
		printf("After %a variables: minimum %a polynomials\n", n, counts[n]):
		print(best[n]):
	end do:
	return S:
end proc:

# Cheks whether vars is a linearly integrable order for the polynomial reduction L
checkIntegrationOrder := proc (L::table, vars::list)
local n, sub:
	for n from 1 to numelems(vars) do
		sub := {op(vars[1 .. n-1])}:
		if not assigned('L'[sub]) then
			error "No reduction data for %1 not available", sub:
		elif not `in`(vars[n], findLinearVariables(L[sub][1])) then
			error "Not linear in %1", vars[n]:
		end if:
		printf("%a. %a: %a polynomials, %a dependent\n",
				n,
				vars[n],
				numelems(L[sub][1]),
				numelems(select(p -> vars[n] in indets(p), L[sub][1]))):
	end do:
	printf("Final polynomials:\n"):
	sub := {op(vars[1 .. numelems(vars)])}:
	print(L[sub][1]):
end proc:

# L is a polynomial reduction; returns the sets of variables that can be integrated out linearly along suitable sequences
# Necessary when L was computed also including non-linear projections
findReachables := proc(L::table)
local todo,result,var,key,vars:
	todo := stack[new]():
	result := {{}}:
	vars := indets(L[{}][1]):
	stack[push]({}, todo):
	while not stack[empty](todo) do
		key := stack[pop](todo):
		for var in (findLinearVariables(L[key][1]) union (vars minus (indets(L[key][1]) union key))) do
			if key union {var} in result then next: fi:
			result := result union {key union {var}}:
			if assigned('L'[key union {var}]) then
					stack[push](key union {var}, todo):
			fi:
		end do:
	end do:
	return result:
end proc:

# Returns the two element sets (a <> b) of the form {a, b} with a in A and b in B
cartprod := proc(A::set, B::set)
local a, b:
	return {seq(seq({a,b}, b in (B minus {a})), a in A)}:
end proc:

# Implementation of the compatibility graph (cg) method of Francis' unpublished paper (efficiently realizes the approximation of Landau varieties by two-dimensional projections)
# if given, bound is a set serving as an upper bound for the landau variety of the target of the projection; passing a bound will eliminate all calls to factors() in favor of divides()
cgSingleReduction := proc(G::list, var, bound := false)
local S, C, s, c, i, f, u, e, Snew:
global _hyper_verbosity:
	# S = Irreducible polynomials (nodes), C = compatibilities (edges)
	S := G[1]:
	C := G[2]:
	# Construct the new sets of polynomials s, a table of the irreducible components indexed by the resultant arguments
	s := table():
	for f in S do
		if degree(f, var)>1 then
			WARNING("Computing Landau-varieties for non-linear projection"):
			# The discriminant is the resultant [f,f'] divided by f's leading coefficient
			s[{f}] := irreducibles({discrim(f, var)}, {}, bound):
		end:
		s[{infinity, f}] := irreducibles({lcoeff(f, var)}, {}, bound):
		s[{0, f}] := irreducibles({coeff(f, var, 0)}, {}, bound):
	end do:
	for e in C do
		if (degree(e[1],var)>0) and (degree(e[2],var)>0) then
			s[e] := irreducibles({resultant(e[1], e[2], var)}, {}, bound):
		else
			s[e] := {}:
		end if:
	end do:
	Snew := `union`(seq(s[e], e in indices(s, 'nolist'))):
	if _hyper_verbosity>99 then
		printf("    %a polynomials\n", numelems(Snew)):
	end if:
	# For the new compatibilities, we need to consider all resultants (not just compatible ones!)
	for e in combinat[choose](S, 2) minus C do
		if (degree(e[1],var)>0) and (degree(e[2],var)>0) then
			s[e] := irreducibles({resultant(e[1], e[2], var)}, {}, Snew):
		else
			s[e] := {}:
		end if:
	end do:
	if _hyper_verbosity>99 then
		printf("    finished computation of all pairwise resultants"):
	end if:
	# Compatibilities between the irreducible factors themselves of a resultant or discriminant
	c := `union`(seq(combinat[choose](s[e], 2), e in indices(s, 'nolist'))):
	# remaining compatibilities
	c := `union`(c, seq(cartprod(s[{0, f}], s[{infinity, f}]), f in S)):
	c := `union`(c, seq(cartprod(s[{0, e[1]}], s[{0, e[2]}]), e in combinat[choose](S, 2))):
	c := `union`(c, seq(cartprod(s[{infinity, e[1]}], s[{infinity, e[2]}]), e in combinat[choose](S, 2))):
	c := `union`(c, seq(cartprod(s[e], s[{0, e[1]}] union s[{0, e[2]}] union s[{infinity, e[1]}] union s[{infinity, e[2]}]), e in combinat[choose](S, 2))):
	if _hyper_verbosity>99 then
		printf("    %a compatibilities among resultant factors, discriminant factors and leading/constant coefficients\n", numelems(c)):
	end if:
#	for f in S do
#		for u in combinat[choose](S minus {f}, 2) do
#			c := c union cartprod(s[{f, u[1]}], s[{f, u[2]}]):
#		end do:
#	end do:
	f := {seq(op(`union`(cartprod(s[{u[1],u[2]}], s[{u[1],u[3]}]),cartprod(s[{u[2],u[1]}], s[{u[2],u[3]}]),cartprod(s[{u[3],u[1]}], s[{u[3],u[2]}]))), u in combinat[choose](S, 3))}:
	c := c union f:
	if _hyper_verbosity>99 then
		printf("    %a compatibilities including resultant pairs with at most three grand parents\n", numelems(c)):
	end if:
	# Correction: Compatibilities between Discriminants and var-independent polynomials needed!
	e := {seq(`if`(degree(f,var)>1, op(s[{f}]), NULL), f in S)}:
	u := {seq(`if`(degree(f,var)=0, f, NULL), f in S)}:
	u := cartprod(e,u):
	if _hyper_verbosity>99 then
		printf("    %a new compatibilities from constant-discriminant pairs\n", numelems(u minus c)):
	end if:
	c := c union u:
	# Correction: Compatibilities between resultants and var-independent polynomials needed!
	e := `union`(seq(s[f], f in C)):
	u := {seq(`if`(degree(f,var)=0, f, NULL), f in S)}:
	u := cartprod(e,u):
	if _hyper_verbosity>99 then
		printf("    %a new compatibilities from constant-resultant pairs\n", numelems(u minus c)):
	end if:
	c := c union u:
	return [Snew, c]:
end proc:

# Perform compatibility-Graph reductions for the edge sets given in todo
# if todo is not a list, then it is a set specifying the variables to ignore in the reduction
cgReduction := proc(L::table, _todo := {}, maxDegree::integer := 1)
local vars, e, G, H, dads, i, todo, counter, printInfo:
global _hyper_verbosity, _hyper_verbose_frequency:
	# If no todo is given, automatically detect all missing indices
	if type(_todo, set) then
		if not assigned(evaln(L[{}])) then
			return:
		end if:
		vars := indets(L[{}]) minus _todo:
		dads := {indices(L, nolist)}:
		todo := map(op, [seq(combinat[choose](vars, i) minus dads, i=1..nops(vars))]):
		if _hyper_verbosity>0 then
			printf("No todo-list given; generated %a missing index sets\n", numelems(todo)):
		end if:
	else
		todo := _todo:
	end if:
	counter := 0:
	for vars in todo do
		counter := counter + 1:
		printInfo := counter mod _hyper_verbose_frequency = 0:
		if (_hyper_verbosity>0) and printInfo then
			printf("Projection along %a\n", vars):
		end if:
		printInfo := printInfo and (_hyper_verbosity>1):
		if assigned('L'[vars]) then
			G := L[vars]:
			if printInfo then
				printf("  Using upper bound of %a polynomials already known\n", numelems(G[1])):
			end if:
		else
			G := 0:
		end if:
		# Look for possible projections and make sure to do linears first by putting them to the front of dads
		dads := []:
		for e in vars do
			# Skip sets that were not calculated
			if not assigned(L[vars minus {e}]) then
				if printInfo then
					printf("  skipping uncalculated %a\n", vars minus {e}):
				end if:
				next:
			end if:
			# Sort by maximum degree: lowest first!
			H := max(map(degree, L[vars minus {e}][1], e)):
			if H>maxDegree then
				if printInfo then
					printf("  skipping %a of degree %a in %a\n", vars minus {e}, H, e):
				end if:
				next:
			end if:
			dads := [op(dads), e]:
			i := nops(dads):
			while i>1 do
				if max(map(degree, L[vars minus {dads[i-1]}][1], dads[i-1])) > H then
					dads[i] := dads[i-1]:
					i := i-1:
				else
					break:
				end if:
			end do:
			dads[i] := e:
		end do:
		# Do the projections
		for e in dads do
			if printInfo then
				printf("  projecting along %a, maximal degree: %a\n", e, max(map(degree, L[vars minus {e}][1], e))):
			end if:
			H := cgSingleReduction(L[vars minus {e}], e, `if`(G=0, false, G[1])):
			if G=0 then
				G := H:
			else
				G := [G[1] intersect H[1], G[2] intersect H[2]]:
			end if:
		end do:
		# Leave entry unassigned if no information is available
		if G<>0 then
			L[vars] := G:
		elif printInfo then
			printf("  => No information!\n"):
		end if:
	end do:
end proc:

rescaleVars := proc(poly::ratpoly, vars::set({symbol,typeindex(anything,symbol)}), amount)
local v:
	subs([seq(v=v*amount, v in vars)], poly):
end proc:

# Setup for dimensional regularization: We consider integrands of the form \prod_i ratpoly_i^{n_i}, where n_i is a function of some variables (in which we want do analytically regularize), e.g. epsilon
# frozen is a set of parameters, i.e. those are not integrated over
# expandAt defines around which values of regvars the analytic regularization is to be performed
# maxSdd defines the value below which every divergence is reported (maxSdd = -1 will only report linear divergences or worse); setting maxSdd=infinity reports all sdd's
findDivergences := proc(
integ#::[anything,list([ratpoly,ratpoly])] &under (factors) # Does not work in Maple 15
, frozen::set(symbol) := {}, expandAt::list(symbol=anything) := [], maxSdd := 0)
local vars, S, n, d, t, divs, subzero, subinf, kzero, kinf, sdd, facts, regvars, pre, expandNear, f, projective:
global _hyper_verbosity:
	vars := indets(integ) minus frozen:
	# integ must be a product of powers of ratpoly's; all variables in exponents are assumed to be regularized analytically
	facts := factors(integ):
	pre := facts[1]:
	facts := facts[2]:
	regvars := indets(map2(op, 2, facts)):
	vars := indets(map2(op, 1, facts)) minus regvars:
	if regvars intersect frozen <> {} then
		error "Frozen infinitessimal variables: %1", frozen intersect regvars:
	end if:
	vars := vars minus frozen:
	# Check homogeneity
	projective := true:
	for f in facts do
		n := rescaleVars(numer(f[1]), vars, t):
		d := rescaleVars(denom(f[1]), vars, t):
		if (ldegree(n, t)<>degree(n, t)) or (ldegree(d,t)<>degree(d,t)) then
			WARNING("factor %1 is not homogeneous in the variables %2", f[1], vars):
			projective := false:
		end if:
	end do:
	# Values of the infinitessimal variables at the point we analytically expand about:
	if expandAt=[] then
		expandNear := [seq(f=0, f in regvars)]:
	else
		expandNear := expandAt:
	end if:
	if _hyper_verbosity>0 then
		printf("Analytic regularization around %a\n", expandNear);
	end if:
	# Find divergent sectors
	divs := table():
	for kzero from 0 to numelems(vars) do
		for subzero in combinat[choose](vars, kzero) do
			for kinf from 0 to numelems(vars)-kzero do
				if kzero+kinf=0 then next: fi:
				for subinf in combinat[choose](vars minus subzero, kinf) do
					sdd := kzero - kinf:
					for f in facts do
						n := numer(f[1]):
						d := denom(f[1]):
						sdd := sdd + f[2]*(ldegree(rescaleVars(rescaleVars(n, subzero, t), subinf, 1/t), t) - ldegree(rescaleVars(rescaleVars(d, subzero, t), subinf, 1/t), t)):
					end do:
					sdd := simplify(sdd):
					# Check projectiveness
					if projective and (numelems(vars) = kzero) then
						if (sdd<>0) then
							WARNING("not a projective form; homogeneous but wrong degree %1 instead of %2", sdd - numelems(vars), -numelems(vars)):
						end if:
					end if:
					if eval(sdd, expandNear) <= maxSdd then
						divs[subzero union map(`^`, subinf, -1)] := sdd:
					end if:
				end do:
			end do:
		end do:
	end do:
	# For a projective integrand, remove all sets that scale all variables
	if projective then
		for subzero in select(f->numelems(f) = numelems(vars), [indices(divs, 'nolist')]) do
			divs[subzero] := evaln(divs[subzero]):
		end do:
	end if:
	return eval(divs):
end proc:

dimregPartial := proc(integ, sub::set, sdd::ratpoly)
local f, subinf, subzero:
	subzero, subinf := selectremove(f->op(0,f)<>`^`, sub):
	if map2(op,2,subinf) minus {-1}<>{} then
		error "Unexpected powers: %1", subinf:
	end if:
	subinf := map2(op,1,subinf):
	integ*(sdd-numelems(subzero)+numelems(subinf))/sdd-eval(diff(eval(integ, [seq(var=var*tempRescale,var in subzero), seq(var=var/tempRescale, var in subinf)]), tempRescale), tempRescale=1)/sdd:
#	facts := factors(integ):
#	integ/sdd*(sdd-numelems(sub)-add(f[2]*add(var*diff(f[1], var), var in sub)/f[1], f in facts[2])):
end proc:

# expands in a parameter (into logarithm powers)
expansion := proc(integ, var, toOrder := 0, fromOrder := 0)
local fac, result, f, t:
	fac := factors(integ):
	fac[1] := convert(series(fac[1], var=0), `polynom`, var):
	result := [[fac[1], []]]:
	for f in fac[2] do
		if var in (indets(f[1]) intersect indets(f[2])) then
			error "Invalid term %1, both base and exponent depend on %2", f, var:
		end if:
		result := scalarMul(result, f[1]^(eval(f[2],var=0))):
		if var in indets(f[2]) then
			result := shuffleSymbolic(result, [seq([(-coeff(f[2],var,1)*var)^n/n!, [[-f[1]]$n]], n=0..toOrder)]):
		end if:
		# Remove terms of higher order
		result := [seq([add(var^n*coeff(t[1], var, n), n=0..toOrder), t[2]], t in result)]:
		result := remove(t->t[1]=0, result):
	end do:
	result := [seq([add(var^n*coeff(t[1], var, n), n=fromOrder..toOrder), t[2]], t in result)]:
	result := remove(t->t[1]=0, result):
	result:
end proc:

polyFromZero := proc(zero, var)
local S:
	if op(0, zero)='Root' then
		if op(2, zero)<>var then
			error "Mismatch between zero (Root wrt. %1) and variable %2", op(2,zero),var:
		end if:
	elif var in indets(zero) then
		error "zero %1 depends on %2!", zero, var:
	elif zero=0 then
		return var:
	else
		S := irreducibles({denom(zero)*var - numer(zero)}):
		if numelems(S)<>1 then
			error "The polynomial with zero %1 in %2 does factor - should not happen!", zero, var:
		end if:
		return S[1]:
	end if:
end proc:

# Looks in the reduction L for polynomials for quadratic polynomials that would factor over algebraic extensions of the function field in parameters
suggestDiscriminants := proc(L::table, parameters::set)
local result, d, p, var, key:
	result := {}:
	for key in indices(L, nolist) do
		for p in L[key][1] do
			for var in (indets(p) minus parameters) do
				if degree(p, var)<>2 then
					next:
				end if:
				d := factors(discrim(p, var)):
				# remove perfect squares
				d[2] := select(w->w[2] mod 2 = 1, d[2]):
				d := d[1]*mul(w[1], w in d[2]):
				if indets(d) subset parameters then
					result := result union {d}:
				end if:
			end do:
		end do:
	end do:
	result:
end proc:

# Vertices are assumed to be numbered consecutively; the last Vertex gets deleted from the matrix
graphMatrix := proc(edges::list)
local M, nodeCount, edgeCount, e:
	edgeCount := nops(edges):
	nodeCount := max(seq(op(e), e in edges)):
	M := Matrix(1..edgeCount+nodeCount, 1..edgeCount+nodeCount):
	for e from 1 to nops(edges) do
		M[e,e] := x[e]:
		M[e,edgeCount + edges[e][1]] := 1:
		M[e,edgeCount + edges[e][2]] := -1:
		M[edgeCount + edges[e][1], e] := -1:
		M[edgeCount + edges[e][2], e] := 1:
	end do:
	M[[1..edgeCount+nodeCount-1],[1..edgeCount+nodeCount-1]]:
end proc:

# M is the fixed graph matrix
dodgson := proc(M, Is::set, Js::set, Ks::set)
local E:
	E := LinearAlgebra[RowDimension](M):
	return LinearAlgebra[Determinant](subs([seq(x[k]=0, k in Ks)], M[[op({`$`(1..E)} minus Is)], [op({`$`(1..E)} minus Js)]])):
end proc:
