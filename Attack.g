# ----- Helper functions that don't need to be in ConjugatorPortrait -----

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
TestConjugatorPortraitForParameters := function(G, list_sizes, g_lengths, r_lengths, attempts, k, filename)

	local nucleus, NucleusMaxLength, MaxContractingDepth, M, N, placeholder, PortraitDepthUpperBound, contracting_depth, PermGroups, AreNotConjugateOnLevel,
                ConjugatorEvenFirstLevel, NucleusDistinctLevel, nucleus_distinct_level, N_perms, N_masks, N_portraits, NucleusElementByPermutation, 
		NucleusElementByPortrait, ExtendPortrait, PrunePortrait, ContractingPortrait, ConjugatorPortrait, ConjugatorPortraitRecursive, 
		TestConjugatorPortrait, size, g_len, r_len, result;
	# --- Group-specific computations ---

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
		local depth, extended_portrait1, extended_portrait2;

		if Size(port) = 1 then 
			return [AutomPortrait(port[1]), AutomPortraitDepth(port[1])];              
		else 
			extended_portrait1 := ExtendPortrait(port[2]);
			extended_portrait2 := ExtendPortrait(port[3]); 

			depth := Maximum(extended_portrait1[2], extended_portrait2[2]) + 1;
			
			return [ [port[1], extended_portrait1[1], extended_portrait2[1]], depth ]; 
		fi; 
	end;	

	PrunePortrait := function (port) 
		local pruned_portrait, depth, pruned_1, pruned_2;                                

		if Size(port) = 1 then 
			return [port, 0]; 
		fi;  

		pruned_portrait := port;

		if Size(port[2]) > 1 or Size(port[3]) > 1 then
			pruned_1 := PrunePortrait(port[2]);
			pruned_2 := PrunePortrait(port[3]);

			depth := Maximum(pruned_1[2], pruned_2[2]) + 1;

			pruned_portrait := [port[1], pruned_1[1], pruned_2[1]];
		else
			depth := 1; 
		fi;      

		if pruned_portrait in N_portraits then 
			return [ [NucleusElementByPortrait(pruned_portrait)], 0 ]; 
		fi;

		return [pruned_portrait, depth]; 
	end;

	ContractingPortrait := function(port) 
		local cportrait;
		cportrait := ExtendPortrait(port);
		cportrait := PrunePortrait(cportrait[1]);
		return cportrait;
	end;

	PortraitToMaskBoundaryNonuniform := function(portrait , depth_of_portrait)
		local i , sections, d;
		
		if depth_of_portrait=0 then
			if Length(portrait)=1 then
				return portrait;
			else
				Error("PortraitToMaskBoundaryNonuniform: <depth_of_portrait> cannot be smaller than the depth of the portrait");
			fi;
		fi;

		if Length(portrait)=1 then 
			return Sections(portrait[1], depth_of_portrait); 
		fi;

		d := Length(portrait) - 1;

		sections:=[];

		for i in [1..d] do
			Append(sections, PortraitToMaskBoundaryNonuniform(portrait[i+1],depth_of_portrait-1));
		od;

		return sections;
	end;

	PermutationOfNestedPortrait := function(portrait, depth_of_portrait)
		local i, d, perms, l;

		if depth_of_portrait=1 then
			if Length(portrait)=1 then
				return PermOnLevel(portrait[1], depth_of_portrait);
			else
				return portrait[1];
			fi;
		fi;

		if Length(portrait)=1 then 
			return PermOnLevel(portrait[1], depth_of_portrait); 
		fi;

		d := Length(portrait) - 1;

		perms:=List([1..d],x->PermutationOfNestedPortrait (portrait[x+1], depth_of_portrait-1));

		l := [];

		for i in [1..d] 
			do
				Append(l, List(ListPerm(perms[i],d^(depth_of_portrait-1)),x->x+d^(depth_of_portrait-1)*(i^portrait[1]-1)));
			od;

		return PermList(l);
	end;

	#Recover portrait of secret conjugator
	ConjugatorPortrait:=function( g_list, h_list, key_length )
		local t, branch_count, odd_g_idxs, gh_extended, portrait;
		t := Runtime();
		branch_count := 0;
		contracting_depth := PortraitDepthUpperBound(key_length);

		# Recursively builds portrait of conjugator from lists of conjugate pairs
		ConjugatorPortraitRecursive :=function( g_list, h_list, level)
		
			local sigma_r, sigma_gs, related_r_sections, set_of_related_r_sections, i, new_g_list, new_h_list, g_h_index
				sigma_g, g_sections, h_sections;

			sigma_r := recoveringL1(g_list, h_list);
			if sigma_r = fail then 
				return fail;
			fi;

			#MIGHT NEED TO UPDATE THIS
			if lev = contracting_depth + nucleus_distinct_level then
				return [sigma_r, [placeholder], [placeholder]]; 
			fi;

			#If we get to this point, we know how r acts on the first level
			#Now: figure out which sections of r we need to recover
			sigma_gs := List(g_list, g -> PermOnLevel(g, 1));
			related_r_sections := Orbits(Group(sigma_gs));
			SortBy(related_r_sections, orbit -> Length(orbit)); #arrange from smallest to largest

			#Recover as many sections as needed and fill in the rest
			for set_of_related_r_sections in related_r_sections do 
				for i in set_of_related_r_sections do 
					#Attemptting to recover r_i
					#Need new lists of conjugate pairs
					new_g_list := [];
					new_h_list := [];
					for g_h_index in [1..Size(g_list)] do 
						sigma_g := PermOnLevel(g_list[g_h_index], 1);
						g_sections := Sections(g_list[g_h_index], 1);
						h_sections := Sections(h_list[g_h_index], 1);
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
					portrait_of_r_i := ConjugatorPortraitRecursive(new_g_list, new_h_list, level + 1);
					if portrait_of_r_i = fail then 
						if i = Length(set_of_related_r_sections) then 
							#could not recover any section in this set
							return fail;
						else 
							#try another section in this set
							continue;
						fi;
					fi;

					#If we get here, we have the portrait of r_i.
					#We need to express this as a tree automorphism to compute the other relevant sections.

					

					#got all sections in this set, move onto the next one
					break;
				od;
			od;
			

		end; # End of ConjugatorPortraitRecursive	

		portrait := ConjugatorPortraitRecursive( g_list, h_list, 1);

		# Approximate running time of call to ConjugatorPortrait
		t := Runtime() - t;

		return [portrait, t, branch_count];

	end; # End of ConjugatorPortrait

	# --- testing ---

	TestConjugatorPortrait := function(list_size, g_length, conj_length)
		local successes, i, g_list, r, h_list, gh_extended, number_of_factors, result, r_portrait, depth, time, branches, t;
		successes := 0;
		time := [];
		branches := [];

		for i in [1..attempts] do

			Print("Attempt #", i, "\n");
			t := Runtime();

			g_list := RandomElementList(g_length, G, list_size);
			r := RandomElement(conj_length, G);
			Print("Time to generate elements: ", Runtime() - t, "\n");

			t := Runtime();

			h_list := List(g_list, x -> r^-1*x*r);
			Print("Time to conjugate elements: ", Runtime() -t, "\n");

			t := Runtime();

			if g_length <= conj_length then
				# how many g's do we need to multiply for a g as long as the conjugator?
				number_of_factors := Int(Ceil(Float(conj_length/g_length))); 
				# Pass n_o_f + ( n_o_f mod 2 ) so that if our list is all odds, we get all evens instead
				gh_extended := ExtendLists( g_list, h_list, number_of_factors + (number_of_factors mod 2) );
				Append( g_list, gh_extended[1] );
				Append( h_list, gh_extended[2] );

			elif list_size < 50 then
				gh_extended := ExtendLists( g_list, h_list, 2 );
				# (also means that we double the length when g_length = conj_length)
				Append( g_list, gh_extended[1] );
				Append( h_list, gh_extended[2] );
			fi;

			Print("Time to extend lists: ", Runtime() -t, "\n");


			# ConjugatorPortrait returns list [ [portrait, depth], runtime, branch_count ]
			result := ConjugatorPortrait(g_list, h_list, conj_length);
			Add(time, result[2]);

			if not result[1] = fail then
			    r_portrait := result[1][1];

			    if r_portrait = AutomPortrait(r) then
				successes := successes + 1;
				Print("Success! Runtime = ", result[2], ", branch count = ", result[3], "\n"); 
			    else
				# If a list is returned but it isn't the right portrait, something is wrong
				Error("output is not AutomPortrait");
			    fi;
			fi;

		od;
		
		# [proportion success, average time]
		return [ Float(successes/attempts), Float(Sum(time)/attempts) ];

	end; # End of TestConjugatorPortrait

	
	for size in list_sizes do
		for g_len in g_lengths do
			for r_len in r_lengths do
				result := TestConjugatorPortrait( size, g_len, r_len);
				if filename = "" then
					Print("List Size: ", size, ", g Length: ", g_len, ", Conjugator Length: ", r_len, "; Proportion of Success: ", result[1], ", Avg Time: ", result[2], "\n");
				else
					AppendTo(filename, "List Size: ", size, ", g Length: ", g_len, ", Conjugator Length: ", r_len, "; Proportion of Success: ", result[1], ", Avg Time: ", result[2], "\n");
				fi;
			od;
		od;
	od;

end;





# ---- Functions for testing (load CSP_attack.g first) ----


# Tests the ConjugatorPortrait function in specified group G
TestConjugatorPortrait := function(G, list_size, g_length, conj_length, attempts)
	local successes, i, g_list, r, h_list, result, r_portrait, depth, time, branches, t;
	successes := 0;
	time := [];
	branches := [];

	for i in [1..attempts] do

		Print("Attempt #", i, "\n");
		t := Runtime();

		g_list := RandomElementList(g_length, G, list_size);
		r := RandomElement(conj_length, G);
		Print("Time to generate elements: ", Runtime() - t, "\n");

		t := Runtime();

		h_list := List(g_list, x -> r^-1*x*r);
		Print("Time to conjugate elements: ", Runtime() -t, "\n");


		# ConjugatorPortrait returns list [ [portrait, depth], runtime, branch_count ]
		result := ConjugatorPortrait(g_list, h_list, conj_length);
		Add(time, result[2]);

		if not result[1] = fail then
		    r_portrait := result[1][1];

		    if r_portrait = AutomPortrait(r) then
			successes := successes + 1;
			Print("Success! Runtime = ", result[2], ", branch count = ", result[3], "\n"); 
		    else
			# If a list is returned but it isn't the right portrait, something is wrong
			Error("output is not AutomPortrait");
		    fi;
		fi;

	od;

	# [proportion success, average time]
	return [ Float(successes/attempts), Float(Sum(time)/attempts) ];
end;