LoadPackage("AutomGrp");
N_LETTERS := 2;
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

# ----------------------------------------------------------------------------------------------------
# ------------------------- Testing Function for Lists of Parameters----------------------------------
# ----------------------------------------------------------------------------------------------------
ConjugatorPortrait := function(G, g_list, h_list, r_length, k)

	local nucleus, NucleusMaxLength, MaxContractingDepth, M, N, placeholder, PortraitDepthUpperBound, contracting_depth, PermGroups, AreNotConjugateOnLevel,
        ConjugatorEvenFirstLevel, NucleusDistinctLevel, nucleus_distinct_level, N_perms, N_masks, N_portraits, NucleusElementByPermutation, 
		NucleusElementByPortrait, ExtendPortrait, PrunePortrait, ContractingPortrait, ConjugatorPortrait, ConjugatorPortraitRecursive, 
		TestConjugatorPortrait, size, g_len, r_len, result, TestConjugacyRelationships, recoveringL1, IntersectionOfTuples, L, extended_children,
		ExtendedPortrait, pruned_children, PortraitToMaskBoundaryNonuniform, PermutationOfNestedPortrait, WreathToPortrait, portrait, i, ith_portrait,
		FindAllConjugators;
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
		local ghConjugators, allConj, intersect, i;

		# getting tuples of g and h values
		ghConjugators := FindAllConjugators(PermGroupOnLevel(G, 1), g_t[1], h_t[1]);

		for i in [2..Length(g_t)] do
			# all conjugators of a g/h pair
			allConj := FindAllConjugators(PermGroupOnLevel(G, 1), g_t[i], h_t[i]);
			ghConjugators := Intersection(ghConjugators, allConj);
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

	N_portraits := List(nucleus, n -> AutomPortrait(n)); 

	# function to take portrait of depth 1 ([perm, [word], [word]]) 
	# and if it is in the nucleus, return element of nucleus
	NucleusElementByPortrait := function( port )
	        local i;
	
		for i in [1..Size(nucleus)] do
			if port = N_portraits[i] then 
				return nucleus[i];
			fi;
		od;

		return fail;
	end;

	ExtendPortrait := function(port)
		local depth, extended_children, extended_portrait;

		if Size(port) = 1 then 
			return AutomPortrait(port[1]);              
		else 
			extended_children := List([2..Length(port)], index -> ExtendPortrait(port[index]));
			extended_portrait := [port[1]];
			Append(extended_portrait, extended_children);
			return extended_portrait;
		fi; 
	end;	

	PrunePortrait := function (port) 
		local pruned_portrait, depth, pruned_1, pruned_2;                                

		if Size(port) = 1 then 
			return port; 
		fi;  

		pruned_children := List([2..Length(port)], index -> PrunePortrait(port[index]));
		pruned_portrait := [port[1]];
		Append(pruned_portrait, pruned_children);
		if pruned_portrait in N_portraits then 
			return [ [NucleusElementByPortrait(pruned_portrait)], 0 ]; 
		fi;
		return pruned_portrait;
	end;

	ContractingPortrait := function(port) 
		local cportrait;
		cportrait := ExtendPortrait(port);
		cportrait := PrunePortrait(cportrait);
		return cportrait;
	end;

	PortraitToMaskBoundaryNonuniform := function(portrait , depth_of_portrait)
		local i , sections, lower_sections, top_level_permutation;
		
		#Print("Converting portrait to mask\n");
		#Print("Portrait: ", portrait, "depth: ", depth_of_portrait, "\n");

		if depth_of_portrait=0 then
			if Length(portrait)=1 then
				#Print("Base case. Returning ", portrait, "\n");
				return portrait;
			else
				Error("PortraitToMaskBoundaryNonuniform: <depth_of_portrait> cannot be smaller than the depth of the portrait");
			fi;
		elif depth_of_portrait = 1 then 
			return List([1..N_LETTERS], i -> portrait[i+1][1]);
		fi;


		if Length(portrait)=1 then 
			#Print("Length 1, returning ", Sections(portrait[1], 1), "\n");
			return Sections(portrait[1], 1);
		fi;

		sections:=[];

		for i in [1..N_LETTERS] do
			#Print("Current portrait: ", portrait, ", current depth: ", depth_of_portrait, "\n");
			#Print("i value: ", i, "\n");
			#Print("Next call: ", portrait[i+1], ", ", depth_of_portrait-1, "\n");
			lower_sections := PortraitToMaskBoundaryNonuniform(portrait[i+1],depth_of_portrait-1);
			top_level_permutation := PermActionOnLevel(PermutationOfNestedPortrait(portrait[i+1], depth_of_portrait - 1), depth_of_portrait - 1, 1, N_LETTERS);
			Append(sections, [TreeAutomorphism(lower_sections, top_level_permutation)]);
		od;
		#Print("Returning ", sections);
		return sections;
	end;

	PermutationOfNestedPortrait := function(portrait, depth_of_portrait)
		local i, perms, l, id_sections;

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
		local t, branch_count, odd_g_idxs, gh_extended, portrait;
		t := Runtime();
		branch_count := 0;
		contracting_depth := PortraitDepthUpperBound(key_length);

		# Recursively builds portrait of conjugator from lists of conjugate pairs
		ConjugatorPortraitRecursive :=function( g_list, h_list, level)
		
			local sigma_r, sigma_gs, related_r_sections, set_of_related_r_sections, i, new_g_list, new_h_list, g_h_index,
				sigma_g, sections_of_r, lhs, g, h, next, rhs, portrait_of_r_i,
				cycle_member, number_recovered, h_index, new_section, new_r_sections, newer_r_sections, r_i_permutation,
				r_i_sections, r_i, index, sigma_h, orbits_under_sigma_gs, current_portrait_depth;

			sigma_r := recoveringL1(g_list, h_list);
			Print("On level ", level, " recovered sigma_r as ", sigma_r, "\n");
			if sigma_r = fail then 
				return fail;
			fi;

			current_portrait_depth := contracting_depth + nucleus_distinct_level - level;
			if current_portrait_depth = 0 then
				Print("Base case. Returning this portrait: ", [sigma_r, [placeholder], [placeholder]], "\n");
				return [sigma_r, [placeholder], [placeholder]]; 
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
				for i in set_of_related_r_sections do 
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
					Print("Making recursive call to level ", level + 1, "\n");
					Print("New gs: ", new_g_list, "\n");
					Print("New hs: ", new_h_list, "\n");
					portrait_of_r_i := ConjugatorPortraitRecursive(new_g_list, new_h_list, level + 1);
					if portrait_of_r_i = fail then 
						if i = Length(set_of_related_r_sections) then 
							#could not recover any section in this set
							Print("Failed to recover sections at level ", level, "\n");
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
					Print("r_i_sections: ", r_i_sections, "\n");
					Print("current_portrait_depth: ", current_portrait_depth, "\n");
					r_i := TreeAutomorphism(r_i_sections, r_i_permutation);
					Print("Section of r number ", i, ": ", r_i, "\n");
					sections_of_r[i] := r_i;
					new_r_sections := [i];
					newer_r_sections := [];
					number_recovered := 1;
					while number_recovered < Length(set_of_related_r_sections) do
						for index in new_r_sections do 
							for g_h_index in [1..Length(g_list)] do 
								g := g_list[g_h_index];
								sigma_g := PermOnLevel(g, 1);
								h := h_list[g_h_index];
								sigma_h := PermOnLevel(h, 1);
								cycle_member := index^sigma_g;
								h_index := index^sigma_r;
								Print("Current g value: ", g, "\n");
								Print("Current h value: ", h, "\n");
								new_section := Section(g, index)^-1*sections_of_r[index]*Section(h, h_index);
								while cycle_member <> index do 
									if not (IsBound(sections_of_r[cycle_member])) then
										Print("Section of r number ", cycle_member, ": ", new_section, "\n");
										sections_of_r[cycle_member] := new_section;
										number_recovered := number_recovered + 1;
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
			Print("On level ", level, ", ecovered these sections of r: ", sections_of_r, "\n");
			Print("Returning this portrait, ", WreathToPortrait(sections_of_r, sigma_r, current_portrait_depth + 1), "\n");
			return WreathToPortrait(sections_of_r, sigma_r, current_portrait_depth + 1);

		end; # End of ConjugatorPortraitRecursive	

		portrait := ContractingPortrait(ConjugatorPortraitRecursive( g_list, h_list, 1));

		# Approximate running time of call to ConjugatorPortrait
		t := Runtime() - t;

		return [portrait, t];

	end; # End of ConjugatorPortrait
	return ConjugatorPortrait(g_list, h_list, r_length)[1];
end;

#G := AutomatonGroup("a = (1, 1)(1, 2), b = (a, c), c = (a, d), d = (1, b)");
#g_list := [a*b*a*c, d*a*c, a*c*a*b*a*d*a*c*a, a*b*a*d*a, a*c, b*a*c*a, d*a];
#r := a*c*a;
#h_list := List(g_list, g -> r^-1*g*r);
#Print(ConjugatorPortrait(G, g_list, h_list, 3, 2));

G := AutomatonGroup("a = (1, 1)(1, 2), b = (a, c), c = (a, d), d = (1, b)");
g_list := [ b^-1*c^-1, d^-3, a^-1*c^-2*d^-1, b*c, d, a*d, b*a];
r := d*a;
h_list := List(g_list, g -> g^r);
 
Print("Final result: ", ConjugatorPortrait(G, g_list, h_list, 3, 2));