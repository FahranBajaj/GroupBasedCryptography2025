LoadPackage("AutomGrp");
Reset(GlobalMersenneTwister,CurrentDateTimeString()); #new random seed
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

	local N_LETTERS, nucleus, MaxContractingDepth, M, ContractingDepthStatApprox, L,
		placeholder, PortraitDepthUpperBound, AreNotConjugateOnLevel, nucleus_distinct_level,
		N_perms, PrunePortrait, ConjugatorPortrait, TestConjugacyRelationships, 
		recoveringL1, IntersectionOfConjugators, PermutationOfNestedPortrait, 
		PortraitProduct, PortraitInverse, FindAllConjugators, AssignNucleusElements, 
		PortraitToNucleusByPermutation, ElemsWithDistinctPerms, ElemWithPermutation;

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
        Print("Found the random elements\n");
		N := N*1.0;

		elem_depths := [];
			
        i := 0;
        for g in gs do
            ed := AutomPortraitDepth(g);
            i := i + 1;
            Print("Done with ", i, "elements.\n");
            Append(elem_depths, [ed]);
        od;
        
        x_bar := Sum(elem_depths)/Length(elem_depths);
        differences := List(elem_depths, x -> (x-x_bar)^2);
        variance := Sum(differences)/(Length(gs)-1);
        sigma := Sqrt(variance*1.0);

        # contracting depth with probability 1 - epsilon (from their paper)
        cd_UB := Int(Ceil(x_bar + (Sqrt((N^(1/3)+1)/(epsilon*(N^(1/3)))) + Sqrt((N^(1/3)+1)/(epsilon*N)))*sigma));

		return [elem_depths, cd_UB];
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
		local centralizer, r;

		centralizer := Centralizer(G, g); # centralizer of g
		r := RepresentativeAction(G, g, h, CONJUGATION_ACTION);
		return Elements(RightCoset(centralizer, r));
	end;

	IntersectionOfConjugators := function(g_t, h_t)
		local sigma_g, sigma_h, ghConjugators, allConj, i;

		# getting tuples of g and h values
		ghConjugators := FindAllConjugators(PermGroupOnLevel(G, 1), PermOnLevel(g_t[1], 1), PermOnLevel(h_t[1], 1));
		i := 2;
		while Length(ghConjugators) > 1 and i <= Length(g_t) do
			# all conjugators of a g/h pair
			sigma_g := PermOnLevel(g_t[i], 1);
			sigma_h := PermOnLevel(h_t[i], 1);
			allConj := FindAllConjugators(PermGroupOnLevel(G, 1), sigma_g, sigma_h);
			ghConjugators := Intersection(ghConjugators, allConj);
			i := i + 1;
		od;
		return ghConjugators;
	end;

	#Helper method to recover action of r on the first level. Takes one (g, h) pair and 
	#possible sigma_r and tests the conjugacy relationships given by each sigma_r
	TestConjugacyRelationships := function(g, h, candidate_sigma_r)
		local sigma_g, cycle_structure, orbits, sizesWithMultipleCycles, 
		fixed_points, size, orbits_of_size, valid_sigma_r, sigma_r, valid, 
		orbit, lhs, rhs, current_index, section;
		sigma_g := PermOnLevel(g, 1);
		cycle_structure := CycleStructurePerm(sigma_g);
		orbits := Orbits(Group(sigma_g));
		sizesWithMultipleCycles := []; 
		fixed_points := [1..N_LETTERS];
		if not IsOne(sigma_g) then
			SubtractSet(fixed_points, MovedPoints(sigma_g));
		fi;
		if Length(fixed_points) > 1 then 
			Append(sizesWithMultipleCycles, [1]);
		fi;
		for size in [1..Length(cycle_structure)] do
			if IsBound(cycle_structure[size]) and cycle_structure[size] > 1 then 
				#cycle_structure[1] is number of cycles of length 2
				Append(sizesWithMultipleCycles, [size + 1]);
			fi;
		od;
		valid_sigma_r := [];
		for sigma_r in candidate_sigma_r do
			valid := true;
			for size in sizesWithMultipleCycles do
				if size = 1 then 
					orbits_of_size := List(fixed_points, pt -> [pt]);
				else 
					orbits_of_size := Filtered(orbits, orbit -> Length(orbit) = size);
				fi;
				for orbit in orbits_of_size do
					#g_{a_1}g_{a_2}...g_{a_n} ~ h_{b_1}h_{b_2}...h_{b_n}
					lhs := One(G); #identity
					rhs := One(G);
					current_index := orbit[1];
					for section in [1..size] do 
						lhs := lhs * Section(g, current_index);
						rhs := rhs * Section(h, current_index^sigma_r);
						current_index := current_index^sigma_g;
					od;
					if AreNotConjugateOnLevel(lhs, rhs, 4) then
						valid := false;
						break;
					fi;
				od;
				if not valid then 
					break;
				fi;
			od;
			if valid then
				Append(valid_sigma_r, [sigma_r]);
			fi;
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
		if portrait_depth > nucleus_distinct_level then
			return Concatenation([portrait[1]], List([1..N_LETTERS], i -> AssignNucleusElements(portrait[i+1], portrait_depth - 1)));
		fi;

		return [PortraitToNucleusByPermutation(portrait)];
	end;

	#Modified from Arsalan
	PrunePortrait := function(portrait)
		local nucleus, nucleus_identified, prune;

		nucleus := List(GroupNucleus(G), x-> [x]) ; 
		nucleus_identified := List(nucleus , x -> [x,Concatenation([PermOnLevel(x[1],1)] , List([1..N_LETTERS],y->[Sections(x[1])[y]])) ]) ;

		prune := function(p) 
			local p_int , i ; 
			p_int := [] ;
			if p in nucleus then 
				return p ;
			else 
				p_int := Concatenation([p[1]] , List([1..N_LETTERS] , x-> prune(p[x+1]))) ;
				for i in [1..Length(nucleus_identified)] do 
						if p_int = nucleus_identified[i][2] then
							return nucleus_identified[i][1];
						fi;
					od;
				return p_int ;
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

	PermutationOfNestedPortrait := function(portrait, depth_of_portrait)
		local i, perms, l;

		if Length(portrait)=1 then 
			return PermOnLevel(portrait[1], 1); 
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

	ElemsWithDistinctPerms := function(elems)
		local perms_seen, indices_to_return, i, perm;
		perms_seen := NewDictionary(PermOnLevel(elems[1], 1), false, SymmetricGroup(N_LETTERS));
		indices_to_return := [];
		for i in [1..Length(elems)] do	
			perm := PermOnLevel(elems[i], 1);
			if not KnowsDictionary(perms_seen, perm) then 
				AddDictionary(perms_seen, perm);
				Append(indices_to_return, [i]);
			fi;
		od;
		return indices_to_return;
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
		local portrait, cportrait, ConjugatorPortraitRecursive, contracting_depth,
			gs_hs_to_multiply, new_g_list, new_h_list, i, idxs, gs, hs, portrait_of_r;

		contracting_depth := PortraitDepthUpperBound(key_length);

		# Recursively builds portrait of conjugator from lists of conjugate pairs
		ConjugatorPortraitRecursive :=function(g_list, h_list, level)
		
			local sigma_r, sigma_gs, related_r_sections, elems_with_distinct_perms, set_of_related_r_sections, 
				i, new_g_list, new_h_list, g_h_index, sigma_g, sections_of_r, 
				lhs, g, h, next, rhs, portrait_of_r_i, cycle_member, number_recovered, 
				h_index, new_section, new_r_sections, newer_r_sections, r_i_permutation, 
				r_i_sections, r_i, index, sigma_h, orbits_under_sigma_gs, 
				current_portrait_depth, j, section_index;

			sigma_r := recoveringL1(g_list, h_list);
			if sigma_r = fail then 
				return fail;
			fi;

			current_portrait_depth := contracting_depth + nucleus_distinct_level - level;
			if current_portrait_depth = 0 then
				return Concatenation([sigma_r], List([1..N_LETTERS], i -> [placeholder])); 
			fi;

			#If we get to this point, we know how r acts on the first level
			#Now: figure out which sections of r we need to recover
			sigma_gs := List(g_list, g -> PermOnLevel(g, 1));
			orbits_under_sigma_gs := Orbits(Group(sigma_gs), [1..N_LETTERS]);
			related_r_sections := ShallowCopy(orbits_under_sigma_gs); #original was immutable
			SortBy(related_r_sections, orbit -> Length(orbit)); #arrange from smallest to largest

			#Recover as many sections as needed and fill in the rest
			elems_with_distinct_perms := ElemsWithDistinctPerms(g_list);
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
						if IsOne(g) then
							continue;
						fi;
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
						Append(new_g_list, [lhs]);
						Append(new_h_list, [rhs]);
					od;
					if Length(new_g_list) = 0 then	
						return fail;
					fi;
                    Print("On level ", level, ", making recursive call to level ", level + 1, "\n");
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
					#We need to express this as a tree automorphism to compute the other relevant sections.
					sections_of_r[i] := portrait_of_r_i;
					new_r_sections := [i];
					newer_r_sections := [];
					number_recovered := 1;
					while number_recovered < Length(set_of_related_r_sections) do
						for index in new_r_sections do 
							for g_h_index in elems_with_distinct_perms do 
								g := g_list[g_h_index];
								sigma_g := PermOnLevel(g, 1);
								h := h_list[g_h_index];
								sigma_h := PermOnLevel(h, 1);
								cycle_member := index^sigma_g;
								h_index := index^sigma_r;
								#g_{index}^-1 * r_{index} * h_{h_index}
								if not (IsBound(sections_of_r[cycle_member])) then 
									new_section := PortraitProduct(PortraitProduct(PortraitInverse(AutomPortrait(Section(g, index))), sections_of_r[index]), AutomPortrait(Section(h, h_index)));
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
		cportrait := AssignNucleusElements(portrait, contracting_depth + nucleus_distinct_level);
		cportrait := PrunePortrait(cportrait);
		return cportrait;

	end; # End of ConjugatorPortrait
	return ConjugatorPortrait(g_list, h_list, r_length);
end;

new_autom_gr := function(T_d, numGenerators, oneProb)
    # T_d: d-ary tree, numGenerators: <= 40,

    local possible_gens, sections, S_d, identity, weightedSections, num1s, numOtherGen, currentGen, i, j, myGens, currentAut;

    # ex: AutomatonGroup([ [ 1, 2, ()], [ 1, 2, (1,2) ] ], [ "a", "b" ]); (a=1, b=2, etc)
    # setup for a new automaton group
    possible_gens := ["1", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t"]; # deal with 1!

    S_d := SymmetricGroup(T_d);

    sections := [];
    identity := [];
    Append(identity, List([1..T_d], x -> 1));
    Append(identity, [One(S_d)]);
    Append(sections, [identity]);

    # getting correct probability of 1s
    weightedSections := [];
    num1s := Int(oneProb*1000.0);
    numOtherGen := Int((1-oneProb)*1000.0/(numGenerators*1.0));

    Append(weightedSections, List([1..num1s], x -> 1));
    for i in [2..(numGenerators + 1)] do
        Append(weightedSections, List([1..numOtherGen], x -> i));
    od;

    # making lists
    for i in [2..(numGenerators+1)] do  # make some generators! skipping identity
        currentGen := [];

        for j in [1..T_d] do  # make some sections!
            # OLD: Append(currentGen, [Random([1..(numGenerators+1)])]);   # CHANGE THIS TO USE PROBABILITY!
            Append(currentGen, [Random(weightedSections)]);
        od;

        Append(currentGen, [Random(Elements(S_d))]);  # appending random permutation!
        Append(sections, [currentGen]);
    od;

    # getting generators
    myGens := List([1..(numGenerators+1)], i -> possible_gens[i]);

    # new automaton group!
    currentAut := AutomatonGroup(sections, myGens);
    
    return currentAut;
end;

RandomContractingGroup := function(T_d, numGenerators, maxNucleusSize, oneProb)
    # T_d: d-ary tree, numGenerators: <= 20, maxNucleusSize: where to quit, numTries: how many groups to generate
    # oneProb: Probability of a section being 1
    local candidateGroup, nucleus;

    while true do 
        candidateGroup := new_autom_gr(T_d, numGenerators, oneProb);
        nucleus := FindNucleus(candidateGroup, maxNucleusSize, false);
        if nucleus <> fail then 
            return candidateGroup;
        fi;
    od;
end;

G_LENS := [10];
R_LENS := [50];
LIST_SIZES := [50];
DIFFERENT_GROUPS := 20;
ONE_PROBS := [0.9, 0.8, 0.7, 0.6, 0.5, 0.4, 0.3];
TRIALS := 10;
MAX_NUCLEUS_SIZE := 30;
TREE_SIZES := [5];
NUM_GENERATORS := [4];

f := OutputTextFile("random_group_success_data.csv", true);
#header: g_len,r_len,list_size,tree_size,one_prob,num_generators,max_nucleus_size,nucleus_size,trials,number_recovered

#placeholder for global variable
G := AutomatonGroup("a = (1)");
for list_size in LIST_SIZES do
	for g_len in G_LENS do
		for r_len in R_LENS do 
            for tree_size in TREE_SIZES do 
                for one_prob in ONE_PROBS do 
                    for num_generators in NUM_GENERATORS do 
                        for i in [1..DIFFERENT_GROUPS] do 
                            G := RandomContractingGroup(tree_size, num_generators, MAX_NUCLEUS_SIZE, one_prob);
                            number_recovered := 0;
                            for trial in [1..TRIALS] do
                                gs := RandomElementList(g_len, g_len, G, list_size);
                                r := RandomElement(r_len, G);
                                hs := List(gs, g -> r^-1*g*r);
                                #Print("Set up example. First g: ", gs[1], ", r: ", r, "\n");
                                recovered_portrait := ConjugatorPortrait(G, gs, hs, r_len + 5, 2, true, 0.1, 0, 0);
                                if recovered_portrait <> fail then
                                    if recovered_portrait <> AutomPortrait(r) then 
                                        Print("Recovered the incorrect portrait for:\nlist of gs: ", gs, "\nlist of hs: ", hs, "\nr: ", r, "\n");
                                    fi;
                                    number_recovered := number_recovered + 1;
                                fi;
                                Print("After ", trial, " trials, we have recovered ", number_recovered, " portraits. Runtime so far: ", Runtime(), ", average runtime per trial: ", Runtime() / trial, "\n");
                            od;
                            Print("For g_len ", g_len, ", r_len ", r_len, ", list_size ", list_size, ", we recovered ", number_recovered, " out of ", TRIALS, " portraits.\n");
                            AppendTo("random_group_success_data.csv", g_len, ",", r_len, ",", list_size, ",", tree_size, ",", one_prob, ",", num_generators, ",", MAX_NUCLEUS_SIZE, ",", Size(GroupNucleus(G)), ",", TRIALS, ",", number_recovered, "\n");
                            #simulate flush
                            CloseStream(f);
                            f := OutputTextFile("random_group_success_data.csv", true);
                        od;
                    od;
                od;
            od;	
		od;
	od;
od;
CloseStream(f);