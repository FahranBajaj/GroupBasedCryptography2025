LoadPackage("AutomGrp");
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

#Slightly modified from 2024 group
RandomElementList := function(min_len, max_len, group, list_size)
 
    local i , j, relations, rule, rules, rules_product, rules_equivalence, 
		generators, family, randomelt, successors, gen, len, rws, letter_rep, 
		starters, element_list;

    element_list := [];
   
    AG_UseRewritingSystem(group);
    relations := FindGroupRelations(group,2);

    relations := Filtered(relations, x -> (Length(Word(x)) <= 3) ); 

    if not relations = [] then
	    AG_AddRelators(group, relations);
    fi;

    rws        := AG_RewritingSystem(group);
    generators := GeneratorsOfMonoid(Image(rws!.mhom));
 
    rules      := AG_RewritingSystemRules(group);
    rules_product := [];
    rules_equivalence := [];
    family     := FamilyObj(Word(One(group)));

    for rule in rules do
	letter_rep := LetterRepAssocWord(rule[1]);
	if Size(letter_rep) = 2 then
		Add(rules_product, letter_rep);
        elif Size(letter_rep) = 1 then
		Add(rules_equivalence, [letter_rep[1], LetterRepAssocWord(rule[2])]);
	fi;
    od;

    starters   := Set([1..Size(generators)]);
    successors := List([1..Size(generators)], x -> Set([1..Size(generators)]) );
   
    # No generator can be followed by an element that will simplify the product 
    for rule in rules_product do
	RemoveSet(successors[rule[1]], rule[2]);
    od;

    # If two generators are equivalent, ignore one
    for rule in rules_equivalence do
	for i in [1..Size(successors)] do	
		RemoveSet(successors[i], rule[1]);
	od;
	successors[rule[1]] := [];
	RemoveSet(starters, rule[1]);
    od;

    for i in [1..list_size] do
	    gen :=  Random(starters);
	    randomelt := [gen];
	 	len := Random([min_len..max_len]);

	    for j in [2..len] do  
		    gen := Random(successors[gen]);
		    Add( randomelt, gen );
	    od;

	    # Changes from denoting generators/inverses as 1, 2, 3.. to 1, -1, 2, -2..
	    randomelt := List( randomelt, x -> (-1)^(x + 1)*Ceil(Float(x/2)) );
	    randomelt := List( randomelt, x -> Int(x) );

	    randomelt := AssocWordByLetterRep(family, randomelt);
	    randomelt := Representative(randomelt, One(group));

	    Add(element_list, randomelt);
    od;

    return element_list;
end;

RandomElement := function(len, group)
    return RandomElementList(len - 5, len + 5, group, 1)[1];
end;

ConjugatorPortrait := function (G, g_list, h_list, r_length, k, use_statistical_approx, epsilon,
								extended_word_length, num_new_pairs)

	local N_LETTERS, nucleus, placeholder, AreNotConjugateOnLevel, L, nucleus_distinct_level,
		N_perms, nucleus_one_down, PrunePortrait, ConjugatorPortrait, 
		TestConjugacyRelationships, recoveringL1, IntersectionOfConjugators, 
		PermutationOfNestedPortrait, PortraitProduct, PortraitInverse, FindAllConjugators, 
		AssignNucleusElements, PortraitToNucleusByPermutation, ElemsWithDistinctPerms, 
		ElemWithPermutation, PruneSingleLevel, functionOutpu, callsToRecoveringL1, 
		callsToTestConjugacy, MaxContractingDepth, ContractingDepthStatApprox, 
		PortraitDepthUpperBound;

	N_LETTERS := DegreeOfTree(G);

	# Finds maximum level at which elements of length <= len contract to nucleus
	MaxContractingDepth := function(len)
		local level, elements, elem_depths;
		AG_UseRewritingSystem(G);
		AG_UpdateRewritingSystem(G, 2);

		elements := ListOfElements(G, len);
		elem_depths := List(elements, x -> AutomPortraitDepth(x));
		level := Maximum(elem_depths);
		return level;
	end;

	ContractingDepthStatApprox := function(N, r_length)
		local gs, cd_UB, elements, elem_depths, ed, x_bar, differences, variance, sigma, g;
		# N: sample size of elements with same length l(g), sigma: standard deviation, x_bar sample mean, epsilon: small
		gs := RandomElementList(r_length, r_length, G, N);
		N := N*1.0;

		elem_depths := [];
			
			for g in gs do
				ed := AutomPortraitDepth(g);
				Append(elem_depths, [ed]);
			od;
			
			x_bar := Sum(elem_depths)/Length(elem_depths);

			differences := List(elem_depths, x -> (x-x_bar)^2);
			variance := Sum(differences)/(Length(gs)-1);
			sigma := Sqrt(variance*1.0);

			# contracting depth with probability 1 - epsilon (from their paper)
			cd_UB := Int(Ceil(x_bar + (Sqrt((N^(1/3)+1)/(epsilon*(N^(1/3)))) + Sqrt((N^(1/3)+1)/(epsilon*N)))*sigma));

		return cd_UB;
	end;

	PortraitDepthUpperBound := function(n)
		local M, N, a, len;

		if use_statistical_approx then
			return ContractingDepthStatApprox(100, r_length);
		fi;

		M := Maximum(List(nucleus, x -> Length(Word(x))));
		N := MaxContractingDepth(k*M);
		if n <= k*M then
			return MaxContractingDepth(n);
		fi;

		a := LogInt(n, k) + 1;
		len := Int(Ceil( Float( (k/k-1)*M ) ));
		return N*a + MaxContractingDepth( len );
	end;

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
			local centralizer, r, c;
			centralizer := Centralizer(G, g); # centralizer of g
			r := RepresentativeAction(G, g, h, CONJUGATION_ACTION);
	        return RightCoset(centralizer,r);
	end;
	
	IntersectionOfConjugators := function(g_t, h_t)
	    local sigma_g, sigma_h, ghConjugators, allConj, i;
	
	    # getting tuples of g and h values
	    ghConjugators := FindAllConjugators(PermGroupOnLevel(G, 1), PermOnLevel(g_t[1], 1), PermOnLevel(h_t[1], 1));
	    i := 2;
	    while Size(ghConjugators) > 1 and i <= Length(g_t) do
	        # all conjugators of a g/h pair
	        sigma_g := PermOnLevel(g_t[i], 1);
	        sigma_h := PermOnLevel(h_t[i], 1);
	        allConj := FindAllConjugators(PermGroupOnLevel(G, 1), sigma_g, sigma_h);
	        ghConjugators := Intersection(ghConjugators, allConj);
	        i := i + 1;
	    od;
	    return Elements(ghConjugators);
	end;

	#Helper method to recover action of r on the first level. Takes one (g, h) pair and 
	#possible sigma_r and tests the conjugacy relationships given by each sigma_r
	TestConjugacyRelationships := function(g, h, candidate_sigma_r)
		local sigma_g, cycle_structure, orbits, sizesWithMultipleCycles, size,
			relationsToPerms, dictKeys, RotateProduct, sigma_r, orbits_of_size,
			orbit, current_index, lhs, rhs, i, permsWithRelation, j, permsWithKey,
			valid_sigma_r;

		sigma_g := PermOnLevel(g, 1);
		cycle_structure := CycleStructurePerm(sigma_g);
		orbits := OrbitsPerms([sigma_g], [1..N_LETTERS]);
		sizesWithMultipleCycles := []; 
		if N_LETTERS - Length(MovedPoints(sigma_g)) > 1 then 
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
			lhs := Product(List(dictKeys[i][1], index -> Section(g, index)));
			rhs := Product(List(dictKeys[i][2], index -> Section(h, index)));
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
	
	recoveringL1 := function(g_t, h_t)
		local possibleRs, i, sigma_g, fixed_points;

		#Get possible sigma_r by looking at permutations that could conjugate all sigma_g/sigma_h pairs
		possibleRs := IntersectionOfConjugators(g_t, h_t);

		if Length(possibleRs) = 1 then
			return possibleRs[1];
		else
			#Narrow down possibilities for sigma_r by looking at conjugacy relationships between sections
			i := 1;
			while i <= Length(g_t) and Length(possibleRs) > 1 do
				sigma_g := PermOnLevel(g_t[i], 1);            
				fixed_points := [1..N_LETTERS];
					if not IsOne(sigma_g) then
						SubtractSet(fixed_points, MovedPoints(sigma_g));
					fi;
				if fixed_points > 1 or Maximum(CycleStructurePerm(sigma_g)) > 1 then 
					possibleRs := TestConjugacyRelationships(g_t[i], h_t[i], possibleRs);
				fi;
				i := i + 1;
			od;
			if Length(possibleRs) = 1 then 
				return possibleRs[1];
			else
				return fail;
			fi;

		fi;
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
		Error("Did not reach element of the nucleus at contracting_depth");	
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

	PruneSingleLevel := function(portrait)
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
				p_int := Concatenation([p[1]] , List([1..N_LETTERS] , x-> p[x+1]));
				identified_nuc_elem := IdentifyNucleusElement(p_int);
				if identified_nuc_elem <> fail then 
					return identified_nuc_elem;
				fi;
				return p_int;
			fi;
		end;

		return prune(portrait);
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

	ElemsWithDistinctPerms := function(gs, hs)
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

		permToElems := NewDictionary(PermOnLevel(gs[1], 1), true, SymmetricGroup(N_LETTERS));
		perms := [];
		for i in [1..Length(gs)] do 
			perm := PermOnLevel(gs[i], 1);
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
	
	ElemWithPermutation := function(g_s, h_s, sigma)
		local G, H, permGroup, F, FGenerators, FToPerm, FToG, FToH, sigmaInF, g, h;
		G := Group(g_s);
		H := Group(h_s);
		permGroup := PermGroupOnLevel(G, 1);
		F := FreeGroup(Length(g_s));
		FGenerators := GeneratorsOfGroup(F);
		FToPerm := GroupHomomorphismByImagesNC(F, permGroup, FGenerators, List(g_s, g -> PermOnLevel(g, 1)));
		FToG := GroupHomomorphismByImagesNC(F, G, FGenerators, g_s);
		FToH := GroupHomomorphismByImagesNC(F, H, FGenerators, h_s);
		sigmaInF := PreImagesRepresentative(FToPerm, sigma);
		g := FToG(sigmaInF);
		h := FToH(sigmaInF);
		return [g, h];
	end;

	#Recover portrait of secret conjugator
	ConjugatorPortrait:=function(short_g_list, short_h_list, key_length )
		local portrait, ConjugatorPortraitRecursive, contracting_depth,
			gs_hs_to_multiply, new_g_list, new_h_list, i, idxs, gs, hs;

		contracting_depth := PortraitDepthUpperBound(key_length);
		Print("Contracting depth is: ", contracting_depth, "\n");
		Print("Nucleus distinct level is: ", nucleus_distinct_level, "\n");

		# Recursively builds portrait of conjugator from lists of conjugate pairs
		ConjugatorPortraitRecursive :=function(g_list, h_list, level)
		
			local sigma_r, sigma_gs, related_r_sections, elems_with_distinct_perms, set_of_related_r_sections, 
				i, new_g_list, new_h_list, g_h_index, sigma_g, sections_of_r, g_h_pair, 
				lhs, g, h, next, rhs, portrait_of_r_i, cycle_member, number_recovered, 
				h_index, new_section, new_r_sections, newer_r_sections, r_i_permutation, 
				r_i_sections, r_i, index, sigma_h, orbits_under_sigma_gs, 
				current_portrait_depth, j, section_index, portrait_of_r;

			sigma_r := recoveringL1(g_list, h_list);
			if sigma_r = fail then 
				return fail;
			fi;

			current_portrait_depth := contracting_depth + nucleus_distinct_level - level;
			if current_portrait_depth = 0 then
				portrait_of_r :=  Concatenation([sigma_r], List([1..N_LETTERS], i -> [placeholder])); 
				if nucleus_distinct_level = 1 then 
					portrait_of_r := AssignNucleusElements(portrait_of_r, 1);
				fi;
				return portrait_of_r;
			fi;

			#If we get to this point, we know how r acts on the first level
			#Now: figure out which sections of r we need to recover
			sigma_gs := List(g_list, g -> PermOnLevel(g, 1));
			orbits_under_sigma_gs := Orbits(Group(sigma_gs), [1..N_LETTERS]);
			related_r_sections := ShallowCopy(orbits_under_sigma_gs); #original was immutable
			SortBy(related_r_sections, orbit -> Length(orbit)); #arrange from smallest to largest

			#Recover as many sections as needed and fill in the rest
			elems_with_distinct_perms := ElemsWithDistinctPerms(g_list, h_list);
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
						sigma_g := PermOnLevel(g, 1);
						h := h_list[g_h_index];
						#if (a_1, ..., a_n) is a cycle in sigma_g and b_i = sigma_r(a_i) then
						#(g_{a_1}...g_{a_n})^r_{a_1} = h_{b_1}...h_{b_n}
						lhs := Section(g, i);
						rhs := Section(h, i^sigma_r);
						next := i^sigma_g;
						while next <> i do 
							lhs := lhs*Section(g, next);
							rhs := rhs*Section(h, next^sigma_r);
							next := next^sigma_g;
						od;

						#easy way to avoid adding identities to list
						if Length(Word(lhs)) = 0 then 
							continue;
						fi;
						Append(new_g_list, [lhs]);
						Append(new_h_list, [rhs]);
					od;
					if Length(new_g_list) = 0 then 
						return fail;
					fi;
					portrait_of_r_i := ConjugatorPortraitRecursive(new_g_list, new_h_list, level + 1);
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
								sigma_g := PermOnLevel(g, 1);
								h := g_h_pair[2];
								sigma_h := PermOnLevel(h, 1);
								cycle_member := index^sigma_g;
								h_index := index^sigma_r;
								#g_{index}^-1 * r_{index} * h_{h_index}
								if not (IsBound(sections_of_r[cycle_member])) then 
									new_section := PortraitProduct(PortraitProduct(PortraitInverse(AutomPortrait(Section(g, index))), sections_of_r[index]), AutomPortrait(Section(h, h_index)));
									if level <= contracting_depth then 
										new_section := AssignNucleusElements(new_section, current_portrait_depth);
									fi;
									if level < contracting_depth then 
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
										new_section := PortraitProduct(PortraitProduct(PortraitInverse(AutomPortrait(Section(g, cycle_member))), new_section), AutomPortrait(Section(h, h_index)));
										if level <= contracting_depth then 
											new_section := AssignNucleusElements(new_section, current_portrait_depth);
										fi;
										if level < contracting_depth then 
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
			portrait_of_r := Concatenation([sigma_r], sections_of_r);
			if level = contracting_depth + 1 then 
				portrait_of_r := AssignNucleusElements(portrait_of_r, nucleus_distinct_level);
			elif level < contracting_depth + 1 then 
				portrait_of_r := PruneSingleLevel(portrait_of_r);
			fi;
			return portrait_of_r;

		end; #End of ConjugatorPortraitRecursive

		new_g_list := [];	
		new_h_list := [];	

		for i in [1..num_new_pairs] do
			idxs := List( [1..extended_word_length], x -> Random([1..Size(short_g_list)]) );
			gs := List(idxs, x -> short_g_list[x]);
			hs := List(idxs, x -> short_h_list[x]);
			Add(new_g_list, Product(gs));
			Add(new_h_list, Product(hs));	
		od;

		gs_hs_to_multiply := List(new_g_list, g -> ElemWithPermutation(short_g_list, short_h_list, PermOnLevel(g, 1)^-1));
		new_g_list := List([1..Length(new_g_list)], i -> new_g_list[i]*gs_hs_to_multiply[i][1]);
		new_h_list := List([1..Length(new_h_list)], i -> new_h_list[i]*gs_hs_to_multiply[i][2]);
		Append(new_g_list, short_g_list);
		Append(new_h_list, short_h_list);

		portrait := ConjugatorPortraitRecursive(new_g_list, new_h_list, 1);
		if portrait = fail then 
			return fail;
		fi;
		return portrait;
	end; # End of ConjugatorPortrait
	return ConjugatorPortrait(g_list, h_list, r_length);
end;

#A simplified example
G := AutomatonGroup("a23 = (a23, 1, 1)(2, 3), a13 = (1, a13, 1)(1, 3), a12 = (1, 1, a12)(1, 2)"); #Hanoi 3 Group
AG_UseRewritingSystem(G);
AG_UpdateRewritingSystem(G, 2);
Reset(GlobalMersenneTwister,CurrentDateTimeString()); #new random seed
g_list := List([1..10], i -> Random(G));
r := Product(List([1..10], i -> Random(G)));
h_list := List(g_list, g -> r^-1*g*r);
final := ConjugatorPortrait(G, g_list, h_list, 30, 2, false, 1, 3, 50); #r is probably not of length more than 20
Print("r: ", r, "\n");
Print("Portrait of r: ", AutomPortrait(r), "\n");
Print("Portrait we found: ", final, "\n");
Print("Correct? ", AutomPortrait(r) = final, "\n");