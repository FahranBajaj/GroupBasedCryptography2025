LoadPackage("AutomGrp", false);
CONJUGATION_ACTION := OnPoints; # action is conjugation

# Returns true if list L contains no repeat elements 
NoRepeats := function(L)
	local i, j, no_repeats;

	no_repeats:= true;
	for i in [1..Size(L)-1] do
		for j in [i+1..Size(L)] do
			if L[i] = L[j] then
				# if 2 elements match, all elements do not differ
				no_repeats := false;
				return no_repeats;
			fi;
		od;
	od;
	return no_repeats;
end;

ConjugatorPortrait := function (G, g_list, h_list, g_length, r_length, stabilizedLevels, contracting_depth)

	local N_LETTERS, nucleus, L, AreNotConjugateOnLevel, nucleus_distinct_level,
		N_perms, PrunePortrait, ConjugatorPortrait, TestConjugacyRelationships, 
		recoveringL1, IntersectionOfConjugators, PermutationOfNestedPortrait, 
		PortraitProduct, PortraitInverse, FindAllConjugators, AssignNucleusElements, 
		PortraitToNucleusByPermutation, ElemsWithDistinctPerms, placeholder,
		nucleus_one_down, PruneNLevels, PermActionAtVertex, BuildPortrait;

	N_LETTERS := DegreeOfTree(G);

	AreNotConjugateOnLevel:=function(a, b, max_level)
		local perm_group, level;
		for level in [1..max_level] do
			perm_group := PermGroupOnLevel(G, level);
			if not IsConjugate(PermGroupOnLevel(G, level), PermOnLevel(a, level), PermOnLevel(b, level)) then
				# Return true if NOT conjugate 
				return true; 
			fi;
		od;
		return false;
	end;

	FindAllConjugators := function(G, g, h)
		local centralizer, r;

		centralizer := Centralizer(G, g); # centralizer of g
		r := RepresentativeAction(G, g, h, CONJUGATION_ACTION);
		return RightCoset(centralizer, r);
	end;

	IntersectionOfConjugators := function(g_t, h_t, level)
        local sigma_g, sigma_h, ghConjugators, allConj, i;

        # getting tuples of g and h values
        ghConjugators := FindAllConjugators(PermGroupOnLevel(G, level), PermOnLevel(g_t[1], level), PermOnLevel(h_t[1], level));
        i := 2;
        while Size(ghConjugators) > 1 and i <= Length(g_t) do
            # all conjugators of a g/h pair
            sigma_g := PermOnLevel(g_t[i], level);
            sigma_h := PermOnLevel(h_t[i], level);
            allConj := FindAllConjugators(PermGroupOnLevel(G, level), sigma_g, sigma_h);
            ghConjugators := Intersection(ghConjugators, allConj);
            i := i + 1;
        od;
        if Size(ghConjugators) = 1 then 
            return ghConjugators[1];
        fi;
        return Elements(ghConjugators);
    end;

	#Helper method to recover action of r on the first level. Takes one (g, h) pair and 
	#possible sigma_r and tests the conjugacy relationships given by each sigma_r
	TestConjugacyRelationships := function(g, h, candidate_sigma_r, level)
		local sigma_g, cycle_structure, orbits, sizesWithMultipleCycles, size,
			relationsToPerms, dictKeys, RotateProduct, sigma_r, orbits_of_size,
			orbit, current_index, lhs, rhs, i, permsWithRelation, j, permsWithKey,
			valid_sigma_r;

		sigma_g := PermOnLevel(g, level);
		cycle_structure := CycleStructurePerm(sigma_g);
		orbits := OrbitsPerms([sigma_g], [1..N_LETTERS^level]);
		sizesWithMultipleCycles := []; 
		if N_LETTERS^level - Length(MovedPoints(sigma_g)) > 1 then 
			Append(sizesWithMultipleCycles, [1]);
		fi;
		for size in [1..Length(cycle_structure)] do
			if IsBound(cycle_structure[size]) and cycle_structure[size] > 1 then 
				#cycle_structure[1] is number of cycles of length 2
				Append(sizesWithMultipleCycles, [size + 1]);
			fi;
		od;

		relationsToPerms := NewDictionary([[1], [1]], true);
		dictKeys := [];

		#Helper method to put each relation g_{i1}g_{i2}...g_{in} ~ h_{j1}h_{j2}...h{jn}
		#into a canonical form where the smallest index comes first.
		RotateProduct := function(factors)
			local min;
			min := Minimum(factors);
			while factors[1] <> min do 
				Append(factors, [factors[1]]);
				Remove(factors, 1);
			od;
		end;

		for sigma_r in candidate_sigma_r do
			for size in sizesWithMultipleCycles do
				orbits_of_size := Filtered(orbits, orbit -> Length(orbit) = size);
				for orbit in orbits_of_size do
					current_index := orbit[1];
					lhs := [];
					rhs := [];
					for i in [1..size] do 
						Append(lhs, [current_index]);
						Append(rhs, [current_index^sigma_r]);
						current_index := current_index^sigma_g;
					od;
					RotateProduct(lhs);
					RotateProduct(rhs);
					if KnowsDictionary(relationsToPerms, [lhs, rhs]) then 
						Append(LookupDictionary(relationsToPerms, [lhs, rhs]), [sigma_r]);
					else 
						AddDictionary(relationsToPerms, [lhs, rhs], [sigma_r]);
						Append(dictKeys, [[lhs, rhs]]);
					fi;
				od;
			od;
		od;

		#sizesWithMultipleCycles is increasing, so 
		#dictKeys is already sorted from short relations to long ones. 
		i := 1;
		valid_sigma_r := ShallowCopy(candidate_sigma_r);
		while Length(valid_sigma_r)  > 1 and i <= Length(dictKeys) do 
			lhs := Product(List(dictKeys[i][1], index -> Sections(g, level)[index]));
			rhs := Product(List(dictKeys[i][2], index -> Sections(h, level)[index]));
			if AreNotConjugateOnLevel(lhs, rhs, 2) then 
				permsWithRelation := LookupDictionary(relationsToPerms, dictKeys[i]);
				SubtractSet(valid_sigma_r, permsWithRelation);
				#looping backwards because we will remove elements of dictKeys
				for j in Reversed([i+1..Length(dictKeys)]) do 
					permsWithKey := LookupDictionary(relationsToPerms, dictKeys[j]);
					SubtractSet(permsWithKey, permsWithRelation);
					if Length(permsWithKey) = 0 then 
						Remove(dictKeys, j);
					fi;
				od;
			fi;
			i := i + 1;
		od;
		return valid_sigma_r;
	end;
        

	recoveringL1 := function(g_t, h_t, currentLevelOfAttack)
        local UniqueOnLevel, current_level, possibleRs, i, sigma_g, 
        fixed_points, level;
		
        UniqueOnLevel := function(possibleRs, bigLevel, smallLevel)
			local firstAction, i;

            firstAction := PermActionOnLevel(possibleRs[1], bigLevel, smallLevel, N_LETTERS);
			i := 2;
			while i <= Length(possibleRs) do 
				if PermActionOnLevel(possibleRs[i], bigLevel, smallLevel, N_LETTERS) <> firstAction then 
					return false;
				fi; 
				i := i + 1;
			od;
			return true;
        end;

        for current_level in [Maximum(1, stabilizedLevels - currentLevelOfAttack)..Maximum(1, stabilizedLevels - currentLevelOfAttack) + 4] do 
            #Get possible sigma_r by looking at permutations that could conjugate all sigma_g/sigma_h pairs
			#This is only useful if we are on a deep enough level that permutations will be nontrivial
			if current_level >= stabilizedLevels - currentLevelOfAttack + 2 then 
				possibleRs := IntersectionOfConjugators(g_t, h_t, current_level);
			else 
				possibleRs := Elements(PermGroupOnLevel(G, current_level));
			fi;
			#this if statement will usually be false so may as well check it before
			#looping through levels in reversed order
            if UniqueOnLevel(possibleRs, current_level, 1) then
                for level in Reversed([2..current_level]) do 
					if UniqueOnLevel(possibleRs, current_level, level) then 
						return [level, PermActionOnLevel(possibleRs[1], current_level, level, N_LETTERS)];
					fi;
				od;
				return [1, PermActionOnLevel(possibleRs[1], current_level, 1, N_LETTERS)];
            fi;
            #Narrow down possibilities for sigma_r by looking at conjugacy relationships between sections
            i := 1;
            while i <= Length(g_t) and not UniqueOnLevel(possibleRs, current_level, 1) do
                sigma_g := PermOnLevel(g_t[i], current_level);            
                fixed_points := [1..N_LETTERS^current_level];
                    if not IsOne(sigma_g) then
                        SubtractSet(fixed_points, MovedPoints(sigma_g));
                    fi;
                if fixed_points > 1 or Maximum(CycleStructurePerm(sigma_g)) > 1 then 
                	possibleRs := TestConjugacyRelationships(g_t[i], h_t[i], possibleRs, current_level);
                fi;
                i := i + 1;
            od;
            if UniqueOnLevel(possibleRs, current_level, 1) then
                for level in Reversed([2..current_level]) do 
					if UniqueOnLevel(possibleRs, current_level, level) then 
						return [level, PermActionOnLevel(possibleRs[1], current_level, level, N_LETTERS)];
					fi;
				od;
				return [1, PermActionOnLevel(possibleRs[1], current_level, 1, N_LETTERS)];
            fi;
        od;
        return fail;
    end;

	# Finds the level at which all elements of the nucleus differ in permutation
	nucleus := GroupNucleus(G);
	placeholder := nucleus[1];
	nucleus_distinct_level := 1;
	while true do	
		L := List(nucleus, x -> PermOnLevel(x, nucleus_distinct_level));
		if NoRepeats(L) then
			break;
		else
			nucleus_distinct_level := nucleus_distinct_level + 1;
		fi;
	od;

    PermutationOfNestedPortrait := function(portrait, depth_of_portrait)
		local i, perms, l;

		if Length(portrait)=1 then 
			return PermOnLevel(portrait[1], depth_of_portrait); 
		fi;

		if depth_of_portrait=1 then
			return portrait[1];
		fi;

		perms:=List([1..N_LETTERS],x->PermutationOfNestedPortrait (portrait[x+1], depth_of_portrait-1));

		l := [];

		for i in [1..N_LETTERS] 
			do
				Append(l, List(ListPerm(perms[i],N_LETTERS^(depth_of_portrait-1)),x->x+N_LETTERS^(depth_of_portrait-1)*(i^portrait[1]-1)));
			od;

		return PermList(l);
	end;

	N_perms := List(nucleus, x -> PermOnLevel(x, nucleus_distinct_level));

	PortraitToNucleusByPermutation := function( port )
		local portrait_permutation, i;

		portrait_permutation := PermutationOfNestedPortrait(port, nucleus_distinct_level);
	
		for i in [1..Size(nucleus)] do
			if portrait_permutation = N_perms[i] then
				return nucleus[i];
			fi;
		od;
		#Error("Did not reach element of the nucleus at contracting_depth");	
        return nucleus[1];
	end;

	#given portrait with a bunch of placeholders, replace with nucleus elements
	AssignNucleusElements := function(portrait, portrait_depth)
		#unwrap layers of portrait that are not necessarily nucleus elements
		if Length(portrait) = 1 then 
			return portrait;
		fi;
		if portrait_depth > nucleus_distinct_level then
			return Concatenation([portrait[1]], List([1..N_LETTERS], i -> AssignNucleusElements(portrait[i+1], portrait_depth - 1)));
		fi;

		return [PortraitToNucleusByPermutation(portrait)];
	end;

	#Modified from Arsalan
	nucleus_one_down := List(nucleus , x -> [[x],Concatenation([PermOnLevel(x,1)] , List([1..N_LETTERS],y->[PortraitToNucleusByPermutation([Sections(x)[y]])])) ]) ;
	PrunePortrait := function(portrait)
		local IdentifyNucleusElement, prune, identified_nuc_elem;

		IdentifyNucleusElement := function(p_int)
			#Assumption: p_int is a portrait of depth greater than 0
			local nucleus_elem, i;
			for nucleus_elem in nucleus_one_down do 
				if p_int[1] = nucleus_elem[2][1] then 
					#permutations match
					i := 2;
					while i <= N_LETTERS + 1 and Length(p_int[i]) = 1 and Word(p_int[i][1]) = Word(nucleus_elem[2][i][1]) do 
						i := i + 1;
					od;
					if i = N_LETTERS + 2 then 	
						return nucleus_elem[1];
					fi;
				fi;
			od;
			return fail;
		end;

		prune := function(p) 
			local p_int , i ; 
			p_int := [] ;
			if Length(p) = 1 then 
				return p;
			else 
				p_int := Concatenation([p[1]] , List([1..N_LETTERS] , x-> prune(p[x+1])));
				identified_nuc_elem := IdentifyNucleusElement(p_int);
				if identified_nuc_elem <> fail then 
					return identified_nuc_elem;
				fi;
				return p_int;
			fi;
		end;

		return prune(portrait);
	end;

	PruneNLevels := function(portrait, n)
		local IdentifyNucleusElement, prune, identified_nuc_elem;

		IdentifyNucleusElement := function(p_int)
			#Assumption: p_int is a portrait of depth greater than 0
			local nucleus_elem, i;
			for nucleus_elem in nucleus_one_down do 
				if p_int[1] = nucleus_elem[2][1] then 
					#permutations match
					i := 2;
					while i <= N_LETTERS + 1 and Length(p_int[i]) = 1 and Word(p_int[i][1]) = Word(nucleus_elem[2][i][1]) do 
						i := i + 1;
					od;
					if i = N_LETTERS + 2 then 	
						return nucleus_elem[1];
					fi;
				fi;
			od;
			return fail;
		end;

		prune := function(p, n) 
			local p_int , i ; 
			p_int := [] ;
			if Length(p) = 1 then 
				return p;
			else 
				if n > 1 then 
					p_int := Concatenation([p[1]] , List([1..N_LETTERS] , x-> prune(p[x+1], n - 1)));
				else 
					p_int := Concatenation([p[1]] , List([1..N_LETTERS] , x -> p[x+1]));
                fi;
				identified_nuc_elem := IdentifyNucleusElement(p_int);
				if identified_nuc_elem <> fail then 
					return identified_nuc_elem;
				fi;
				return p_int;
			fi;
		end;

		return prune(portrait, n);
	end;

	PortraitProduct := function(p1, p2)
		local product ;
		product := function(portrait_1, portrait_2)
			if not IsPerm(portrait_1[1]) and not IsPerm(portrait_2[1]) then
				return AutomPortrait(portrait_1[1]*portrait_2[1]) ;
			fi;
			if IsPerm(portrait_1[1]) and IsPerm(portrait_2[1]) then
				return Concatenation([portrait_1[1]*portrait_2[1]], List([1..N_LETTERS], k->product(portrait_1[k+1] , portrait_2[k^(portrait_1[1])+1])));
			fi;
			if not IsPerm(portrait_1[1]) and IsPerm(portrait_2[1]) then
				return product(Concatenation([Perm(portrait_1[1])],List(Sections(portrait_1[1]),x->[x])),portrait_2);
			fi;
			if not IsPerm(portrait_2[1]) and IsPerm(portrait_1[1]) then
				return product(portrait_1,Concatenation([Perm(portrait_2[1])],List(Sections(portrait_2[1]),x->[x])));	
			fi;
		end;
		return product(p1,p2) ;
	end;

	PortraitInverse := function(p)
		local inverse ;
		inverse := function(portrait)
			local k ;
			if not IsPerm (portrait[1]) then 
				return [portrait[1]^-1] ; 
			fi;
			if IsPerm(portrait[1]) then 
				return Concatenation([portrait[1]^-1], List([1..N_LETTERS], x-> inverse(portrait[x^(portrait[1]^-1)+1]) ) );
			fi;
		end;
		return inverse(p) ;
	end;

	ElemsWithDistinctPerms := function(gs, hs, level)
		local Argmin, permToElems, perms, i, perm, pairs_to_return, elemsWithPerm, argmin;
		Argmin := function(list, func)
			local argmin, min, i, newVal;
			argmin := 1;
			min := func(list[1]);
			i := 2;
			while i <= Length(list) do 
				newVal := func(list[i]);
				if newVal < min then 
					min := newVal;
					argmin := i;
				fi;
				i := i + 1;
			od;
			return argmin;
		end;

		permToElems := NewDictionary(PermOnLevel(gs[1], level), true, SymmetricGroup(N_LETTERS^level));
		perms := [];
		for i in [1..Length(gs)] do 
			perm := PermOnLevel(gs[i], level);
			if KnowsDictionary(permToElems, perm) then 
				Append(LookupDictionary(permToElems, perm), [[gs[i], hs[i]]]);
			else
				AddDictionary(permToElems, perm, [[gs[i], hs[i]]]);
				Append(perms, [perm]);
			fi;
		od;

		pairs_to_return := [];
		for perm in perms do 
			elemsWithPerm := LookupDictionary(permToElems, perm);
			argmin := Argmin(elemsWithPerm, x -> Length(Word(x[1])));
			Append(pairs_to_return, [elemsWithPerm[argmin]]);
		od;
		SortBy(pairs_to_return, x -> Length(Word(x[1])));
		return pairs_to_return;
	end;

	PermActionAtVertex := function(perm, bigLevel, vertex)
		local topLevelAction, topLevelReset, permSplitBySection, permAsList,
			singleSubtreePerm, nextVertex;

		topLevelAction := PermActionOnLevel(perm, bigLevel, 1, N_LETTERS);
		if vertex = [] then 
			return topLevelAction;
		fi;
		topLevelReset := PermList(Concatenation(List([1..N_LETTERS], i -> List([1..N_LETTERS^(bigLevel - 1)], j ->  j + (i^(topLevelAction^-1) - 1)*N_LETTERS^(bigLevel - 1)))));
		permSplitBySection := perm * topLevelReset;
		permAsList := ListPerm(permSplitBySection, N_LETTERS^(bigLevel));
		singleSubtreePerm := PermList(List(permAsList{[(vertex[1] - 1)*N_LETTERS^(bigLevel - 1) + 1..vertex[1] * N_LETTERS^(bigLevel - 1)]}, i -> i - (vertex[1] - 1)*N_LETTERS^(bigLevel - 1)));
		nextVertex := ShallowCopy(vertex);
		Remove(nextVertex, 1);
		return PermActionAtVertex(singleSubtreePerm, bigLevel - 1, nextVertex);
	end;

	BuildPortrait := function(perm, recoveryLevel, depthForPortrait, currentVertex, sections)
		if depthForPortrait = 1 then 
			return Concatenation([PermActionAtVertex(perm, recoveryLevel, currentVertex)], sections);
		fi;
		return Concatenation([PermActionAtVertex(perm, recoveryLevel, currentVertex)], List([1..N_LETTERS], i -> BuildPortrait(perm, recoveryLevel, depthForPortrait - 1, Concatenation(currentVertex, [i]), List([(i-1)*N_LETTERS^(depthForPortrait - 1) + 1..i*N_LETTERS^(depthForPortrait - 1)], j -> sections[j]))));
	end;

	#Recover portrait of secret conjugator
	ConjugatorPortrait:=function(short_g_list, short_h_list)
		local portrait, extended_word_length, num_new_pairs, 
			ConjugatorPortraitRecursive, gs_hs_to_multiply, new_g_list, 
			new_h_list, i, idxs, gs, hs, runtime;

        runtime := Runtime();

		# Recursively builds portrait of conjugator from lists of conjugate pairs
		ConjugatorPortraitRecursive :=function(g_list, h_list, level)
		
			local recoveredAction, sigma_r, recoveryLevel, sigma_gs, related_r_sections, 
				onlyPruneNew, elems_with_distinct_perms, set_of_related_r_sections, i, 
				new_g_list, new_h_list, g_h_index, g_h_pair, sigma_g, sections_of_r, 
				lhs, g, h, next, rhs, portrait_of_r_i, cycle_member, number_recovered, 
				h_index, new_section, new_r_sections, newer_r_sections, r_i_permutation, 
				r_i_sections, r_i, index, sigma_h, orbits_under_sigma_gs, 
				current_portrait_depth, j, section_index, portrait_of_r;

			recoveredAction := recoveringL1(g_list, h_list, level);
			if recoveredAction = fail then 
				return fail;
			fi;

			recoveryLevel := recoveredAction[1];
			sigma_r := recoveredAction[2];

			#depth of portraits that we will be returned from recursive calls.
			#At the end of this method, we will return a portrait of depth one more than this. 
			current_portrait_depth := contracting_depth + nucleus_distinct_level - level;
			if current_portrait_depth < recoveryLevel then 
				portrait_of_r := BuildPortrait(sigma_r, recoveryLevel, current_portrait_depth + 1, [], List([1..N_LETTERS^(current_portrait_depth + 1)], i -> [placeholder]));
				if nucleus_distinct_level <= current_portrait_depth + 1 then 
					portrait_of_r := AssignNucleusElements(portrait_of_r, current_portrait_depth + 1);
				fi;
				if nucleus_distinct_level < current_portrait_depth + 1 then 
					portrait_of_r := PrunePortrait(portrait_of_r);
				fi;
				return portrait_of_r;
			fi;

			#If we get to this point, we know how r acts on the first level(s)
			#Now: figure out which sections of r we need to recover
			sigma_gs := List(g_list, g -> PermOnLevel(g, recoveryLevel));
			orbits_under_sigma_gs := Orbits(Group(sigma_gs), [1..N_LETTERS^recoveryLevel]);
			related_r_sections := ShallowCopy(orbits_under_sigma_gs); #original was immutable
			SortBy(related_r_sections, orbit -> Length(orbit)); #arrange from smallest to largest

			if level + recoveryLevel <= contracting_depth + 1 then 
				onlyPruneNew := true;
			else 
				onlyPruneNew := false;
			fi;

			#Recover as many sections as needed and fill in the rest
			elems_with_distinct_perms := ElemsWithDistinctPerms(g_list, h_list, recoveryLevel);
			sections_of_r := [];
			for set_of_related_r_sections in related_r_sections do 
				for section_index in [1..Length(set_of_related_r_sections)] do 
                    i := set_of_related_r_sections[section_index];
					#Attemptting to recover r_i
					#Need new lists of conjugate pairs
					new_g_list := [];
					new_h_list := [];
					for g_h_index in [1..Size(g_list)] do 
						g := g_list[g_h_index];
						sigma_g := PermOnLevel(g, recoveryLevel);
						h := h_list[g_h_index];
						#if (a_1, ..., a_n) is a cycle in sigma_g and b_i = sigma_r(a_i) then
						#(g_{a_1}...g_{a_n})^r_{a_1} = h_{b_1}...h_{b_n}
						lhs := Sections(g, recoveryLevel)[i];
						rhs := Sections(h, recoveryLevel)[i^sigma_r];
						next := i^sigma_g;
						while next <> i do 
							lhs := lhs*Sections(g, recoveryLevel)[next];
							rhs := rhs*Sections(h, recoveryLevel)[next^sigma_r];
							next := next^sigma_g;
						od;
                        #easy way to avoid adding identities to list
						if Length(Word(lhs)) = 0 then 
							if section_index = Length(set_of_related_r_sections) then 
								#could not recover any section in this set
							return fail;
							else 
								#try another section in this set
								continue;
							fi;
						fi;
						Append(new_g_list, [lhs]);
						Append(new_h_list, [rhs]);
					od;
					if Length(new_g_list) = 0 then	
						return fail;
					fi;
					portrait_of_r_i := ConjugatorPortraitRecursive(new_g_list, new_h_list, level + recoveryLevel);
					if portrait_of_r_i = fail then 
						if section_index = Length(set_of_related_r_sections) then 
							#could not recover any section in this set
							return fail;
						else 
							#try another section in this set
							continue;
						fi;
					fi;

					#If we get here, we have the portrait of r_i.
					#We need to compute the other relevant sections.
					sections_of_r[i] := portrait_of_r_i;
					new_r_sections := [i];
					newer_r_sections := [];
					number_recovered := 1;
					while number_recovered < Length(set_of_related_r_sections) do
						for index in new_r_sections do 
							for g_h_pair in elems_with_distinct_perms do 
								g := g_h_pair[1];
								sigma_g := PermOnLevel(g, recoveryLevel);
								h := g_h_pair[2];
								sigma_h := PermOnLevel(h, recoveryLevel);
								cycle_member := index^sigma_g;
								h_index := index^sigma_r;
								#g_{index}^-1 * r_{index} * h_{h_index}
								if not (IsBound(sections_of_r[cycle_member])) then 
									new_section := PortraitProduct(PortraitProduct(PortraitInverse(AutomPortrait(Sections(g, recoveryLevel)[index])), sections_of_r[index]), AutomPortrait(Sections(h, recoveryLevel)[h_index]));
									if onlyPruneNew then 
										new_section := AssignNucleusElements(new_section, current_portrait_depth);
										new_section := PrunePortrait(new_section);
									fi;
								else 
									new_section := sections_of_r[cycle_member];
								fi;
								while cycle_member <> index do 
									if not (IsBound(sections_of_r[cycle_member])) then
										sections_of_r[cycle_member] := new_section;
										number_recovered := number_recovered + 1;
										if number_recovered = Length(set_of_related_r_sections) then 
											break;
										fi;
										Append(newer_r_sections, [cycle_member]);
									fi;
									h_index := h_index^sigma_h;
									#g_{cycle_member}^-1 * new_section * h_{h_index}
									if not (IsBound(sections_of_r[cycle_member^sigma_g])) then 
										new_section := PortraitProduct(PortraitProduct(PortraitInverse(AutomPortrait(Sections(g, recoveryLevel)[cycle_member])), new_section), AutomPortrait(Sections(h, recoveryLevel)[h_index]));
										if onlyPruneNew then 
											new_section := AssignNucleusElements(new_section, current_portrait_depth);
											new_section := PrunePortrait(new_section);
										fi;
									else 
										new_section := sections_of_r[cycle_member^sigma_g];
									fi;
									cycle_member := cycle_member^sigma_g;	
								od;
								if number_recovered = Length(set_of_related_r_sections) then 
									break;
								fi;
							od;
							if number_recovered = Length(set_of_related_r_sections) then 
								break;
							fi;
						od;
						new_r_sections := newer_r_sections;
						newer_r_sections := [];
					od;
					#got all sections in this set, move onto the next one
					break;
				od;
			od;
			
			#If we get this far, we have recovered the action of r on the first level  
			#as well as all of the sections. The last thing we need to do is convert
			#these back into a portrait and return.
			portrait_of_r := BuildPortrait(sigma_r, recoveryLevel, recoveryLevel, [], sections_of_r);
			if onlyPruneNew then 
				portrait_of_r := PruneNLevels(portrait_of_r, recoveryLevel);
			elif level <= contracting_depth + 1 then 
				portrait_of_r := AssignNucleusElements(portrait_of_r, current_portrait_depth + 1);
				if level < contracting_depth + 1 then 
					portrait_of_r := PrunePortrait(portrait_of_r);
				fi;
			fi;
			return portrait_of_r;

		end; #End of ConjugatorPortraitRecursive

		new_g_list := [];	
		new_h_list := [];	
		num_new_pairs := 50;
		if g_length <= r_length then 
			extended_word_length := Int(Ceil(Float(r_length/g_length)));
		else
			extended_word_length := 2;
		fi;

		for i in [1..num_new_pairs] do
			idxs := List( [1..extended_word_length], x -> Random([1..Size(short_g_list)]) );
			gs := List(idxs, x -> short_g_list[x]);
			hs := List(idxs, x -> short_h_list[x]);
			Add(new_g_list, Product(gs));
			Add(new_h_list, Product(hs));	
		od;

		Append(new_g_list, short_g_list);
		Append(new_h_list, short_h_list);

		portrait := ConjugatorPortraitRecursive(new_g_list, new_h_list, 1);;
        runtime := Runtime() - runtime;
		return [portrait, runtime];
	end; # End of ConjugatorPortrait
	return ConjugatorPortrait(g_list, h_list);
end;

AttackWrapper := function(G, g_list, h_list, g_length, r_length, stabilizedLevels, contracting_depth, real_portrait)
	local portraitRecovered;

	portraitRecovered := ConjugatorPortrait(G, g_list, h_list, g_length, r_length, stabilizedLevels, contracting_depth);
	Print("Returned in time!\n");
	if portraitRecovered[1] = fail then 
		Print("Returning ", portraitRecovered, "\n");
		return portraitRecovered;
	elif portraitRecovered[1] = real_portrait then 	
		Print("Returning ", Concatenation([true], [portraitRecovered[2]]), "\n");
		return Concatenation([true], [portraitRecovered[2]]);
	else 
		Print("Returning ", Concatenation([false], [portraitRecovered[2]]), "\n");
		return Concatenation([false], [portraitRecovered[2]]);
	fi;
end;

OnBreak := function () 
    QuitGap(); 
end;

Reset(GlobalMersenneTwister,CurrentDateTimeString()); #new random seed

Read("./ContractingGroupsFound/GroupsToTestMultiLevelAttack.g");
csvForResults := OutputTextFile("MultiLevelAttackResultsWithExtension.csv", true);
incorrectResults := OutputTextFile("IncorrectResults.g", true);

GROUP_REC := GGS_STAB_3_2; 
GROUP_STRING := GROUP_REC.name;
v := GROUP_REC.vector;
R_LENGTHS := [10, 100, 1000];
LIST_SIZES := [10];
TRIALS := 10;
STABILIZED_LEVELS := 4;
G_LENGTH := 3;

G := AutomatonGroup(GROUP_REC.automaton, ["i", "a", "b", "c", "d", "e", "f", "g"]);
nucleusSize := GROUP_REC.nucleusSize;
Print("Group: ", GROUP_STRING, "\n");



RandomWordInGenerators := function(len, num_generators)
    local choicesOfGenerators;
    choicesOfGenerators := List([1..len], i -> Random([1..num_generators]));
    return choicesOfGenerators;
end;

d := Length(v) + 1;
power := v[1];
for j in [1..d] do
    power := power * j;
    
    if power mod d = 1 then 
        lift_power := j;
        break;
    fi;

    power := v[1];
od;

# setting up lifting dictionary

CONJUGATOR_LIFTING_DICTIONARY := NewDictionary(1, true);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, 1, List([1..lift_power], i -> 2));
b_lift := List([1..(d-1)], i -> 1);
Append(b_lift, [2,1]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, 2, b_lift);

NextLevelConjugator := function(wordOfElement)
    local newGeneratorIndices, i;
    newGeneratorIndices := [];

    for i in wordOfElement do 
        Append(newGeneratorIndices, LookupDictionary(CONJUGATOR_LIFTING_DICTIONARY, i));
    od;
    return newGeneratorIndices;
end;

ProductOfPieces := function(pieces)
    local product, piece, conjugatorWord, conjugator, generator, commutator;
    product := One(G);
    for piece in pieces do 
        #piece = [generator, conjugator]
        conjugatorWord := piece[2];
        conjugator := One(G);
        for generator in conjugatorWord do
            if generator = 1 then 
                conjugator := conjugator * a;
            else
                conjugator := conjugator * b;
            fi;
        od;

        product := product*conjugator^-1;
        commutator := piece[1];
        if commutator = 1 then 
            product := product * (a^-1*b^-1*a*b);
        else
            product := product * (b^-1*a^-1*b*a);
        fi;

        product := product * conjugator;
    od;
    return product;
end;

#Computes random stabilizers of the nth level for the GGS group with vector v. 
#All sections at nth level are identity except first one.

#Lifting equations: 
# [b,b^a] = [a,b]^b * [b,a] = ([a,b],1,...,1)
# [b,b^a]^-1 = [a,b] * [b,a]^b = ([b,a],1,...,1)
RandomStabilizerGGSMostlyId := function(level, innerWordLength, conjugatorLength)
    local current_level, current_element, lifted_element, piece, newConjugator,
        commutator;
    current_level := 0;
    #Represent an element of N by list of [generator, conjugator] factors
    #Where each conjugator is a list of numbers representing generators
    current_element := List([1..innerWordLength], i -> [Random([1..2]), RandomWordInGenerators(conjugatorLength, 2)]); # was cL,3
    while current_level < level do 
        lifted_element := [];
        for piece in current_element do 
            #piece = [generator, conjugator]
            newConjugator := NextLevelConjugator(piece[2]);
            commutator := piece[1];

            if commutator = 1 then 
                Append(lifted_element, [[1, Concatenation(List([1..lift_power], i -> 2), newConjugator)]]);
                Append(lifted_element, [[2, newConjugator]]);
            else 
                Append(lifted_element, [[1, newConjugator]]);
                Append(lifted_element, [[2, Concatenation(List([1..lift_power], i -> 2), newConjugator)]]);
            fi;
        od;
        
        current_element := lifted_element;
        current_level := current_level + 1;
    od;
    return ProductOfPieces(current_element);
end;

GroupActionOnLevel := function(level)
    return function(point, g)
        return point^PermOnLevel(g, level);
    end;
end;

ElemMappingAToBOnLevel := function(G, a, b, level)
    local action;
    action := GroupActionOnLevel(level);
    return RepresentativeAction(G, a, b, action);
end;

RandomStabilizerGGS := function(level, degree, innerWordLength, conjugatorLength)
    local liftedSections, product, conjugator, i;
    liftedSections := List([1..degree^level], i -> RandomStabilizerGGSMostlyId(level, innerWordLength, conjugatorLength));
    product := liftedSections[1];
    for i in [2..degree^level] do
        conjugator := ElemMappingAToBOnLevel(G, 1, i, level);
        product := product * liftedSections[i]^conjugator;
    od;
    return product;
end;


RandomElementList := function(len, group, list_size)
	local element_list, generators, i, prod, j;

    element_list := [];
    generators := ShallowCopy(GeneratorsOfGroup(G));
	Append(generators, List(generators, g -> g^-1));

   	for i in [1..list_size] do
		prod := One(group);
		for j in [1..len] do
			prod := prod * Random(generators);
		od;
		Append(element_list, [prod]);
	od;
	return element_list;
end;

RandomElement := function(len, group)
    return RandomElementList(len, group, 1)[1];
end;



for r_length in R_LENGTHS do
	if not LookupDictionary(feasibilities, [GROUP_REC, r_length]) then	
		continue;
	fi;
	contracting_depth := LookupDictionary(depthBounds, [GROUP_REC, r_length]);
	contractingDepthTime := LookupDictionary(depthTimes, [GROUP_REC, r_length]);
    for list_size in LIST_SIZES do 
        Print("r length: ", r_length, ", list size: ", list_size, "\n");
        for trial in [1..TRIALS] do 
            gs := List([1..list_size], i -> RandomStabilizerGGS(STABILIZED_LEVELS - 1, 3, G_LENGTH, G_LENGTH));
            r := RandomElement(r_length, G);
            hs := List(gs, g -> g^r);
            wrapperCall := IO_CallWithTimeout(rec(hours := 1), AttackWrapper, G, gs, hs, G_LENGTH, r_length, STABILIZED_LEVELS, contracting_depth, AutomPortrait(r));
            dataRow := Concatenation(GROUP_STRING, ",", String(nucleusSize), ",", String(G_LENGTH), ",", String(r_length), ",", String(list_size), ",", String(contracting_depth), ",", String(contractingDepthTime));
            if wrapperCall[1] = fail then 
                #unexpected error (probbaly used too much memory?)
                Print("Unexpected error!\n");
                dataRow := Concatenation(dataRow, ",-3\n");
            elif wrapperCall[1] then 
                #didn't time out
                if wrapperCall[2][1] = fail then 
                    #failed
                    dataRow := Concatenation(dataRow, ",0,", String(wrapperCall[2][2]), "\n");
                elif wrapperCall[2][1] then 
                    #function output was correct
                    dataRow := Concatenation(dataRow, ",1,", String(wrapperCall[2][2]), "\n");
                else 
                    #function returned an incorrect portrait
                    AppendTo("IncorrectResults.g", "rec(G := ", G, ", gs := ", gs, ", hs := ", hs, ", g_length := ", g_length, ", r_length := ", r_length, ", r := ", r, ", contracting_depth := ", contracting_depth, "), ");
                    dataRow := Concatenation(dataRow, ",-2,", String(wrapperCall[2][2]), "\n");
                fi;
            else 
                #we timed out
                Print("Timed out!\n");
                dataRow := Concatenation(dataRow, ",-1\n");
            fi;
            AppendTo("MultiLevelAttackResultsWithExtension.csv", dataRow);
        od;
        
    od;
od;

CloseStream(csvForResults);
CloseStream(incorrectResults);
