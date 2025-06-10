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

ConjugatorPortrait := function(G, g_list, h_list, r_length, k)

	local N_LETTERS, nucleus, MaxContractingDepth, M, N, L, placeholder, 
		PortraitDepthUpperBound, AreNotConjugateOnLevel, nucleus_distinct_level,
		N_perms, PrunePortrait, ConjugatorPortrait, TestConjugacyRelationships, 
		recoveringL1, IntersectionOfTuples, PortraitToMaskBoundaryNonuniform, 
		PermutationOfNestedPortrait, WreathToPortrait, FindAllConjugators, 
		AssignNucleusElements, PortraitToNucleusByPermutation;

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


	nucleus := GroupNucleus(G);

	# Find maximum length of elements in the nucleus
	M := Maximum(List(nucleus, x -> Length(Word(x))));
	N := MaxContractingDepth(k*M);

	# Computes upper bound for portrait depth for an element in group G of length n
	# uses max level at which elements of length <= k*M contract
	PortraitDepthUpperBound := function(n)
		local a, len;

		if n <= k*M then
			return MaxContractingDepth(n);
		fi;

		a := LogInt(n, k) + 1;
		len := Int(Ceil( Float( (k/k-1)*M ) ));
		return N*a + MaxContractingDepth( len );
	end;

	placeholder := nucleus[1];

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

	IntersectionOfTuples := function(g_t, h_t)
		local ghConjugators, allConj, i;

		# getting tuples of g and h values
		ghConjugators := FindAllConjugators(PermGroupOnLevel(G, 1), g_t[1], h_t[1]);
		i := 2;
		while Length(ghConjugators) > 1 and i <= Length(g_t) do
			# all conjugators of a g/h pair
			allConj := FindAllConjugators(PermGroupOnLevel(G, 1), g_t[i], h_t[i]);
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
					if AreNotConjugateOnLevel(lhs, rhs, 2) then
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
		local possibleRs, sigma_gs, sigma_hs, i, sigma_g, fixed_points;
		sigma_gs := List(g_t, g -> PermOnLevel(g, 1));
		sigma_hs := List(h_t, h -> PermOnLevel(h, 1));

		#Get possible sigma_r by looking at permutations that could conjugate all sigma_g/sigma_h pairs
		possibleRs := IntersectionOfTuples(sigma_gs, sigma_hs);

		if Length(possibleRs) = 1 then
			return possibleRs[1];
		else
			#Narrow down possibilities for sigma_r by looking at conjugacy relationships between sections
			i := 1;
			while i <= Length(g_t) and Length(possibleRs) > 1 do
				sigma_g := sigma_gs[i];            
				fixed_points := [1..N_LETTERS];
					if not IsOne(sigma_g) then
						SubtractSet(fixed_points, MovedPoints(sigma_g));
					fi;
				if fixed_points > 1 or Maximum(CycleStructurePerm(sigma_gs)) > 1 then 
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

	PortraitToMaskBoundaryNonuniform := function(portrait , depth_of_portrait)
		local i , sections, lower_sections, top_level_permutation;

		if depth_of_portrait=0 then
			if Length(portrait)=1 then
				return portrait;
			else
				Error("PortraitToMaskBoundaryNonuniform: <depth_of_portrait> cannot be smaller than the depth of the portrait");
			fi;
		elif depth_of_portrait = 1 then 
			return List([1..N_LETTERS], i -> portrait[i+1][1]);
		fi;


		if Length(portrait)=1 then 
			return Sections(portrait[1], 1);
		fi;

		sections:=[];

		for i in [1..N_LETTERS] do
			lower_sections := PortraitToMaskBoundaryNonuniform(portrait[i+1],depth_of_portrait-1);
			top_level_permutation := PermActionOnLevel(PermutationOfNestedPortrait(portrait[i+1], depth_of_portrait - 1), depth_of_portrait - 1, 1, N_LETTERS);
			Append(sections, [TreeAutomorphism(lower_sections, top_level_permutation)]);
		od;
		return sections;
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

	WreathToPortrait := function(sections, permutation, depth_for_portrait)
		local i, ith_portrait, portrait;
		if depth_for_portrait = 0 then 
			return [placeholder];
		fi;
		portrait := [permutation];
		for i in [1..N_LETTERS] do 
			ith_portrait := WreathToPortrait(Sections(sections[i], 1), PermOnLevel(sections[i], 1), depth_for_portrait - 1);
			Append(portrait, [ith_portrait]);
		od;

		return portrait;
	end;

	#Recover portrait of secret conjugator
	ConjugatorPortrait:=function( g_list, h_list, key_length )
		local portrait, cportrait, ConjugatorPortraitRecursive, contracting_depth;
		contracting_depth := PortraitDepthUpperBound(key_length);

		# Recursively builds portrait of conjugator from lists of conjugate pairs
		ConjugatorPortraitRecursive :=function( g_list, h_list, level)
		
			local sigma_r, sigma_gs, related_r_sections, set_of_related_r_sections, 
				i, new_g_list, new_h_list, g_h_index, sigma_g, sections_of_r, 
				lhs, g, h, next, rhs, portrait_of_r_i, cycle_member, number_recovered, 
				h_index, new_section, new_r_sections, newer_r_sections, r_i_permutation, 
				r_i_sections, r_i, index, sigma_h, orbits_under_sigma_gs, 
				current_portrait_depth, j, section_index;

			sigma_r := recoveringL1(g_list, h_list);
			#Print("On level ", level, " recovered sigma_r as ", sigma_r, "\n");
			if sigma_r = fail then 
				return fail;
			fi;

			current_portrait_depth := contracting_depth + nucleus_distinct_level - level;
			if current_portrait_depth = 0 then
				#Print("Base case. Returning this portrait: ", Concatenation([sigma_r], List([1..N_LETTERS], i -> [placeholder])), "\n");
				return Concatenation([sigma_r], List([1..N_LETTERS], i -> [placeholder])); 
			fi;

			#If we get to this point, we know how r acts on the first level
			#Now: figure out which sections of r we need to recover
			sigma_gs := List(g_list, g -> PermOnLevel(g, 1));
			orbits_under_sigma_gs := Orbits(Group(sigma_gs), [1..N_LETTERS]);
			related_r_sections := ShallowCopy(orbits_under_sigma_gs); #original was immutable
			SortBy(related_r_sections, orbit -> Length(orbit)); #arrange from smallest to largest

			#Recover as many sections as needed and fill in the rest
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
						Append(new_g_list, [lhs]);
						Append(new_h_list, [rhs]);
					od;
					#Print("Making recursive call to level ", level + 1, "\n");
					#Print("New gs: ", new_g_list, "\n");
					#Print("New hs: ", new_h_list, "\n");
					portrait_of_r_i := ConjugatorPortraitRecursive(new_g_list, new_h_list, level + 1);
					if portrait_of_r_i = fail then 
						if section_index = Length(set_of_related_r_sections) then 
							#could not recover any section in this set
							#Print("Failed to recover sections at level ", level, "\n");
							return fail;
						else 
							#try another section in this set
							continue;
						fi;
					fi;

					#If we get here, we have the portrait of r_i.
					#We need to express this as a tree automorphism to compute the other relevant sections.
					r_i_permutation := PermActionOnLevel(PermutationOfNestedPortrait(portrait_of_r_i, current_portrait_depth), current_portrait_depth, 1, N_LETTERS);
					r_i_sections := PortraitToMaskBoundaryNonuniform(portrait_of_r_i, current_portrait_depth);
					#Print("r_i_sections: ", r_i_sections, "\n");
					#Print("current_portrait_depth: ", current_portrait_depth, "\n");
					r_i := TreeAutomorphism(r_i_sections, r_i_permutation);
					#Print("Section of r number ", i, ": ", r_i, "\n");
					sections_of_r[i] := r_i;
					new_r_sections := [i];
					newer_r_sections := [];
					number_recovered := 0;
					for j in [1..Length(sections_of_r)] do 
						if IsBound(sections_of_r[j]) then 
							if j in set_of_related_r_sections then 
								number_recovered := number_recovered + 1;
							fi;
						fi;
					od;
					while number_recovered < Length(set_of_related_r_sections) do
						for index in new_r_sections do 
							for g_h_index in [1..Length(g_list)] do 
								g := g_list[g_h_index];
								sigma_g := PermOnLevel(g, 1);
								h := h_list[g_h_index];
								sigma_h := PermOnLevel(h, 1);
								cycle_member := index^sigma_g;
								h_index := index^sigma_r;
								#Print("Current g value: ", g, "\n");
								#Print("Current h value: ", h, "\n");
								new_section := Section(g, index)^-1*sections_of_r[index]*Section(h, h_index);
								while cycle_member <> index do 
									if not (IsBound(sections_of_r[cycle_member])) then
										#Print("Section of r number ", cycle_member, ": ", new_section, "\n");
										sections_of_r[cycle_member] := new_section;
										number_recovered := number_recovered + 1;
										Append(newer_r_sections, [cycle_member]);
									fi;
									h_index := h_index^sigma_h;
									new_section := Section(g, cycle_member)^-1 * new_section * Section(h, h_index);
									cycle_member := cycle_member^sigma_g;	
									if number_recovered = Length(set_of_related_r_sections) then 
										break;
									fi;
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
			#Print("On level ", level, ", ecovered these sections of r: ", sections_of_r, "\n");
			#Print("Returning this portrait, ", WreathToPortrait(sections_of_r, sigma_r, current_portrait_depth + 1), "\n");
			#Print("contracting_depth is ", contracting_depth, ", nucleus_distinct_level is ", nucleus_distinct_level, "\n");
			return WreathToPortrait(sections_of_r, sigma_r, current_portrait_depth + 1);

		end; # End of ConjugatorPortraitRecursive	

		portrait := ConjugatorPortraitRecursive(g_list, h_list, 1);
		if portrait = fail then 
			return fail;
		fi;
		cportrait := AssignNucleusElements(portrait, contracting_depth + nucleus_distinct_level);
		cportrait := PrunePortrait(cportrait);

		return cportrait;

	end; # End of ConjugatorPortrait
	return ConjugatorPortrait(g_list, h_list, r_length);
end;

#From 2024 group
RandomElementList := function(len , group, list_size)
 
    local i , j, relations, rule, rules, rules_product, rules_equivalence, generators, family, randomelt, successors,
		gen, rws, letter_rep, starters, element_list;

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
    return RandomElementList(len, group, 1)[1];
end;


G := AutomatonGroup("a=(1, 1, 1, 1)(1,2)(3,4), b=(a,c,a,c), c=(b,1,1,b)");
G_LENS := [10, 100];
R_LENS := [10, 100];
LIST_SIZE := 50;
TRIALS := 100;

for g_len in G_LENS do
    for r_len in R_LENS do 
        number_recovered := 0;
        for trial in [1..TRIALS] do
            gs := RandomElementList(g_len, G, LIST_SIZE);
            r := RandomElement(r_len, G);
            hs := List(gs, g -> r^-1*g*r);
			#Print("Test case is set up!\n");
			#Print("Group is ", G, "\n");
            recovered_portrait := ConjugatorPortrait(G, gs, hs, r_len, 2);
            if recovered_portrait <> fail then
                if recovered_portrait <> AutomPortrait(r) then 
                    Print("Recovered the incorrect portrait for:\nlist of gs: ", gs, "\nlist of hs: ", hs, "\nr: ", r, "\n");
                fi;
                number_recovered := number_recovered + 1;
            fi;
        od;
        Print("For g_len ", g_len, ", r_len ", r_len, " we recovered ", number_recovered, " out of 100 portraits.\n");
    od;
od;
