# Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/portrait_mask_conversion.g");
# Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
# Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/random_element.g");
# Read("C:/Users/savchuk/Documents/GitHub/Group_Based_Crypto/testing.g");

# Read("~/Documents/GitHub/Group_Based_Crypto/portrait_mask_conversion.g");
# Read("~/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
# Read("~/Documents/GitHub/Group_Based_Crypto/random_element.g");
# Read("~/Documents/GitHub/Group_Based_Crypto/testing.g");


# Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/portrait_mask_conversion.g");
# Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/CSP_attack.g");
# Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/random_element.g");
# Read("/Users/llscuderi/Documents/GitHub/Group_Based_Crypto/testing.g");

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


# Returns list of indices of elements having perm (1,2) on 1st level
IdxsOfOdds:=function(g_list)
	local odd_idxs, i;
	odd_idxs:=[];
	for i in [1..Size(g_list)] do	
		if PermOnLevel(g_list[i], 1) = (1,2) then
			Add(odd_idxs, i);
		fi;
	od;
	return odd_idxs;
end;

# Creates new g,h lists of length 50, with new elements multiples of number_of_factors factors of g's 	
ExtendLists:=function(g_list, h_list, number_of_factors)
	local new_g_list, new_h_list, i, idxs, gs, hs;

	new_g_list := [];	
	new_h_list := [];	

	for i in [1..50] do
		idxs := List( [1..number_of_factors], x -> Random([1..Size(g_list)]) );
		gs := List(idxs, x -> g_list[x]);
		hs := List(idxs, x -> h_list[x]);
		Add(new_g_list, Product(gs));
		Add(new_h_list, Product(hs));	
	od;

	return [new_g_list, new_h_list];
end;
	


# ----------------------------------------------------------------------------------------------------
# ------------------------- Testing Function for Lists of Parameters----------------------------------
# ----------------------------------------------------------------------------------------------------
TestConjugatorPortraitForParameters := function(G, list_sizes, g_lengths, r_lengths, attempts, k, filename)

	local nucleus, NucleusMaxLength, MaxContractingDepth, M, N, placeholder, PortraitDepthUpperBound, contracting_depth, PermGroups, AreNotConjugateOnLevel,
                ConjugatorEvenFirstLevel, NucleusDistinctLevel, nucleus_distinct_level, N_perms, N_masks, N_portraits, NucleusElementByPermutation, 
		NucleusElementByPortrait, ExtendPortrait, PrunePortrait, ContractingPortrait, ConjugatorPortrait, ConjugatorPortraitRecursive, 
		TestConjugatorPortrait, size, g_len, r_len, result;

	if filename = "" then
		Print("Group: ", G, "\n");
		Print("k = ", k, "\n");
	else
		AppendTo(filename, "Group: ", G, "\n");
		AppendTo(filename, "k = ", k, "\n");
		AppendTo(filename, "\n");
	fi;

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


	nucleus := FindNucleus(G)[1];

	# Find maximum length of elements in the nucleus
	NucleusMaxLength := function()
		local element_lengths, M; 
		element_lengths:=List(nucleus, x -> Length(Word(x)));
		M:=Maximum(element_lengths);

		return M;
	end;


	M := NucleusMaxLength();

	# For testing different k values: use precomputed N if we have it
	if G = AG_Groups.Basilica and (k=2 or k=4) then
		if k = 2 then
			N := 4;
		else # k = 4
			N := 6; 
		fi;
	elif AutomatonList(G) = AutomatonList(AutomatonGroup("a=(a,a)(1,2), b=(c,b), c=(a,a)")) and (k=2 or k=5) then # If G is Ag775
		if k = 2 then
			N := 5;
		else # k = 5
			N := 7;
		fi;
	elif AutomatonList(G) = AutomatonList(AutomatonGroup("a=(a,a)(1,2), b=(c,a)(1,2), c=(b,a)")) then # If G is Ag2287
		# Do nothing - we don't use N for this group
	else
		N := MaxContractingDepth(k*M);
	fi;
	
        # Computes upper bound for portrait depth for an element in group G of length n
        # uses max level at which elements of length <= k*M contract
        PortraitDepthUpperBound := function(n)
                local a, len;

		if AutomatonList(G) = AutomatonList(AutomatonGroup("a=(a,a)(1,2), b=(c,a)(1,2), c=(b,a)")) then # If G is Ag2287
			if n <= 100 then
				return 18;
			elif n <= 1000 then
				return 19;
			elif n <= 10000 then
				return 22;
			else
				Error("Contracting depth for l(r) > 10000 in Ag2287 unknown");
			fi;
		fi;

                if n <= k*M then
                        return MaxContractingDepth(n);
                fi;

                a := LogInt(n, k) + 1;
                len := Int(Ceil( Float( (k/k-1)*M ) ));
                return N*a + MaxContractingDepth( len );
        end;

	placeholder := nucleus[1];

	PermGroups := List([1..4], x -> PermGroupOnLevel(G,x));
	
	AreNotConjugateOnLevel:=function(a,b)
		local l, Glev;
		for l in [1..Size(PermGroups)] do
			Glev:=PermGroups[l]; 
			if not IsConjugate(Glev, PermOnLevel(a,l), PermOnLevel(b,l)) then
				# Return true if NOT conjugate 
				return true; 
			fi;
		od;
		return false;
	end;

	# We always pass g that's even on the first level
	# Returns true if conjugator is even on the first level, false if odd, fail if fail
	ConjugatorEvenFirstLevel:=function(g,h)
		local g0, g1, h0, h1;
		g0 := Section(g,1);
		g1 := Section(g,2);
				
		h0 := Section(h,1);
		h1 := Section(h,2);

		# Case 1: if the following aren't conjugate, r isn't even
		if AreNotConjugateOnLevel(g0,h0) or AreNotConjugateOnLevel(g1,h1) then
			return false;

		# Case 2: if the following aren't conjugate, r is even
		elif AreNotConjugateOnLevel(g0,h1) or AreNotConjugateOnLevel(g1,h0) then
			return true;
		else
			return fail;
		fi;	
	end;

	# Finds the level at which all elements of the nucleus differ in permutation
	NucleusDistinctLevel := function(G)
		local lev, L;

		lev := 1;
		while true do
			L := List(nucleus, x -> PermOnLevel(x, lev));
			if NoRepeats(L) then
				return lev;
			else
				lev := lev + 1;
			fi;
		od;
	end;

	nucleus_distinct_level := NucleusDistinctLevel(G);
	N_perms := List(nucleus, x -> PermOnLevel(x, nucleus_distinct_level));

	# If a nested portrait is certainly in the nucleus, identify it by permutation on nucleus_distinct_level
	NucleusElementByPermutation := function( port )
		local portrait_permutation, i;

		portrait_permutation := PermutationOfNestedPortrait(port, nucleus_distinct_level);
	
		for i in [1..Size(nucleus)] do
			if portrait_permutation = N_perms[i] then
				return nucleus[i];
			fi;
		od;
	
		Error("Did not reach element of the nucleus at contracting_depth");	
	end;

	N_masks := List(nucleus, x -> mask_function(x,1));
	N_portraits := List(N_masks, x -> MaskToPortrait(x, 1)); 

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


	# --- recovering conjugator ---
    # *******************************************************************************************************************************************
    # *******************************************************************************************************************************************
    # *******************************************************************************************************************************************
    # *******************************************************************************************************************************************
    # *******************************************************************************************************************************************
    # *******************************************************************************************************************************************
    # *******************************************************************************************************************************************
    # *******************************************************************************************************************************************
    # *******************************************************************************************************************************************
    # *******************************************************************************************************************************************
    # *******************************************************************************************************************************************
    # *******************************************************************************************************************************************
    # *******************************************************************************************************************************************
    # *******************************************************************************************************************************************
    # *******************************************************************************************************************************************
    # *******************************************************************************************************************************************

	ConjugatorPortrait:=function( g_list, h_list, key_length )
		local t, branch_count, odd_g_idxs, gh_extended, portrait;
		t := Runtime();
		branch_count := 0;
	
		Print("contracting depth: ", contracting_depth, "\n");

		# Recursively builds portrait of conjugator from lists of conjugate pairs
		ConjugatorPortraitRecursive :=function( g_list, h_list, lev)
		
			local i, ConjEven, perm, g_list_r0, h_list_r0, g_list_r1, h_list_r1, r0, r1,
				r0_portrait, r1_portrait, contracting_portrait, r0_mask, r1_mask, odd_g, odd_h, r0_TA, r1_TA, 
				g0_TA, g1_TA, h0_TA, portrait_depth, nucleus_element, odd_g_idxs;


			odd_g_idxs := IdxsOfOdds( g_list ); # gets indexes of odd gs
			if odd_g_idxs = [] then
				branch_count := branch_count + 1; # all even-- no sigmas
			fi;

			for i in [1..Size(g_list)] do # each element in the gs
				if not i in odd_g_idxs then
					ConjEven := ConjugatorEvenFirstLevel( g_list[i], h_list[i] );  # see if the level above is even or not

                    # got the level above
					if ConjEven = true then
						perm := ();
					elif ConjEven = false then
						perm := (1,2);
					else # couldn't recover
						# If ConjEven failed and we've made it thought the whole list (i.e. failed to recover r each time)
						# return fail, otherwise go to next g_i
						if i = Size(g_list) then
							return fail;
						else
							continue;
						fi;	
					fi;

					if lev = contracting_depth + nucleus_distinct_level then
						return [ [perm, [placeholder], [placeholder]], 1 ]; # done
					fi;
				
					# Build new lists to recover r0
					g_list_r0 := [];
					h_list_r0 := [];

					for i in [1..Size(g_list)] do # for each g_i, finding r_0
						# If g_i is odd on the first level
						if i in odd_g_idxs then
							# If r is even
							if perm = () then
								Add( g_list_r0, Section( g_list[i], 1 )*Section( g_list[i], 2) );
								Add( h_list_r0, Section( h_list[i], 1 )*Section( h_list[i], 2) );
							# If r is odd
							else
								Add( g_list_r0, Section( g_list[i], 1 )*Section( g_list[i], 2) );
								Add( h_list_r0, Section( h_list[i], 2 )*Section( h_list[i], 1) );
							fi;

						# If g_i is even on the first level
						else
							# If r is even 
							if perm = () then
								Add( g_list_r0, Section( g_list[i], 1 ) );
								Add( h_list_r0, Section( h_list[i], 1 ) );
							# If r is odd	
							else
								Add( g_list_r0, Section( g_list[i], 1 ) );
								Add( h_list_r0, Section( h_list[i], 2 ) );
							fi;
						fi;
					od;
							
					# Conjugate pairs (1,1) give us no information- save time by removing
                    # get rid of identities
					for i in [1..Size(g_list_r0)] do
						if IsOne(g_list_r0[i]) then 
							Unbind(g_list_r0[i]);
							Unbind(h_list_r0[i]);
						fi;
					od;

					g_list_r0 := Compacted(g_list_r0);
					h_list_r0 := Compacted(h_list_r0);

					if g_list_r0 = [] then
						# We can't recover r0 with all identities (and shouldn't bother trying)
						r0 := fail;
					else
						# Recursive step: recover portrait of r0
                        # *******************************************************************************************************************************************
                        # VIP- going down a level
						r0 := ConjugatorPortraitRecursive( g_list_r0, h_list_r0, lev+1);
					fi;

					# Now to recover r1
					if not ((r0 = fail) or (Size(odd_g_idxs) = 0)) then # r0 recovered
						
						# If we can recover r1 from r0
						
						r0_portrait := r0[1]; # ?
						portrait_depth := r0[2]; # ?

                        # getting the odd indexes found above ( h is same as g)
						odd_g := g_list[odd_g_idxs[1]];
						odd_h := h_list[odd_g_idxs[1]];

						# If r0_portrait is a nested list (as opposed to one word),
						# make it into a TreeAutomorphism
						if Size(r0_portrait) > 1 then
							r0_mask := PortraitToMask(r0_portrait, portrait_depth );
							r0_TA := TreeAutomorphism(r0_mask[1], r0_mask[2]);
							
							if perm = () then
								# r even: r1 = g0^-1*r0*h0
								g0_TA := Decompose(Section(odd_g, 1), portrait_depth );
								h0_TA := Decompose(Section(odd_h, 1), portrait_depth );	
								r1_TA := g0_TA^-1 * r0_TA * h0_TA;
							else 
								# r odd: r1 = g1*r0*h0^-1
								g1_TA := Decompose(Section(odd_g, 2), portrait_depth );
								h0_TA := Decompose(Section(odd_h, 1), portrait_depth );	
								r1_TA := g1_TA * r0_TA * h0_TA^-1;
							fi;

							r1_mask := mask_function(r1_TA, 1);
							r1_portrait := MaskToPortrait(r1_mask, portrait_depth );
							if lev < contracting_depth + 1 then
								contracting_portrait := ContractingPortrait(r1_portrait);
								r1_portrait := contracting_portrait[1];
								portrait_depth := Maximum( portrait_depth, contracting_portrait[2] );
							fi;
						else
							if perm = () then
								r1_portrait := AutomPortrait(Section(odd_g,1)^-1 * r0_portrait[1] * Section(odd_h,1));
								portrait_depth := Maximum(portrait_depth, AutomPortraitDepth(Section(odd_g,1)^-1 * r0_portrait[1] * Section(odd_h,1)));
							else
								r1_portrait := AutomPortrait(Section(odd_g,2) * r0_portrait[1] * Section(odd_h,1)^-1);
								portrait_depth := Maximum(portrait_depth, AutomPortraitDepth(Section(odd_g,2) * r0_portrait[1] * Section(odd_h,1)^-1));
							fi;
						fi;

					elif (r0 = fail) and (Size(odd_g_idxs) = 0) then
						return fail;
					else 
						# we either have r0 or relations (not both)
						# Build new lists to recover r1
						
						g_list_r1 := [];
						h_list_r1 := [];

						for i in [1..Size(g_list)] do
							# If g_i is odd 
							if i in odd_g_idxs then
								# If r is even
								if perm = () then
									Add( g_list_r1, Section( g_list[i], 2 )*Section( g_list[i], 1) );
									Add( h_list_r1, Section( h_list[i], 2 )*Section( h_list[i], 1) );
								# If r is odd
								else 
									Add( g_list_r1, Section( g_list[i], 2 )*Section( g_list[i], 1) );
									Add( h_list_r1, Section( h_list[i], 1 )*Section( h_list[i], 2) );
								fi;

							# If g_i is even
							else
								# If r is even
								if perm = () then
									Add( g_list_r1, Section( g_list[i], 2 ) );
									Add( h_list_r1, Section( h_list[i], 2 ) );
								# If r is odd
								else
									Add( g_list_r1, Section( g_list[i], 2 ) );
									Add( h_list_r1, Section( h_list[i], 1 ) );
								fi;	
							fi;	
						od;

						# Conjugate pairs (1,1) give us no information
						for i in [1..Size(g_list_r1)] do
							if IsOne(g_list_r1[i]) then 
								Unbind(g_list_r1[i]);
								Unbind(h_list_r1[i]);
							fi;
						od;

						g_list_r1 := Compacted(g_list_r1);
						h_list_r1 := Compacted(h_list_r1);

						if g_list_r1 = [] then
							# We can't recover r0 with all identities (and shouldn't bother trying)
							r1 := fail;
						else
							# Recursive step: recover portrait of r1
							r1 := ConjugatorPortraitRecursive( g_list_r1, h_list_r1, lev+1);
						fi;

						# At this point, if we don't have r1, we don't have r
						if r1 = fail then
							return fail;
						fi;
				
						# Now we decide how we need to use r1, depending on whether we have r0

						if not (r0 = fail) then

							# If we called the recursive function for both r0 and r1
						
							r0_portrait := r0[1];
							r1_portrait := r1[1];
							
							portrait_depth := Maximum(r0[2], r1[2]);
						else
								
							# If we can recover r0 from r1
							
							r1_portrait := r1[1];
							portrait_depth := r1[2];

							odd_g := g_list[odd_g_idxs[1]];
							odd_h := h_list[odd_g_idxs[1]];

							# If r1_portrait is a nested list (as opposed to one word),
							# make it into a TreeAutomorphism
							if Size(r1_portrait) > 1 then
								r1_mask := PortraitToMask(r1_portrait, portrait_depth );
								r1_TA := TreeAutomorphism(r1_mask[1], r1_mask[2]);
								
								if perm = () then
									# r even: r0 = g0*r1*h0^-1
									g0_TA := Decompose(Section(odd_g, 1), portrait_depth );
									h0_TA := Decompose(Section(odd_h, 1), portrait_depth );	
									r0_TA := g0_TA * r1_TA * h0_TA^-1;
								else 
                                    #
									# r odd: r0 = g1^-1*r1*h0
									g1_TA := Decompose(Section(odd_g, 2), portrait_depth );
									h0_TA := Decompose(Section(odd_h, 1), portrait_depth );	
									r0_TA := g1_TA^-1 * r1_TA * h0_TA;
								fi;

								r0_mask := mask_function(r0_TA, 1);
								r0_portrait := MaskToPortrait(r0_mask, portrait_depth );
								if lev < contracting_depth + 1 then
									contracting_portrait := ContractingPortrait(r0_portrait);
									r0_portrait := contracting_portrait[1];
									portrait_depth := Maximum( portrait_depth, contracting_portrait[2] );
								fi;
							else 
								if perm = () then
									r0_portrait := AutomPortrait(Section(odd_g,1) * r1_portrait[1] * Section(odd_h,1)^-1);
									portrait_depth := Maximum(portrait_depth, AutomPortraitDepth(Section(odd_g,1) * r1_portrait[1] * Section(odd_h,1)^-1));
								else
									r0_portrait := AutomPortrait(Section(odd_g,2)^-1 * r1_portrait[1] * Section(odd_h,1));
									portrait_depth := Maximum(portrait_depth, AutomPortraitDepth(Section(odd_g,2)^-1 * r1_portrait[1] * Section(odd_h,1)));
								fi;
							fi;

						fi; # End of deciding how to use r1
						
					fi; # Should have r0_portrait and r1_portrait at this point

					
					if lev = contracting_depth + 1 then
						# on this level, portraits with placeholders become members of the nucleus
						return [ [ NucleusElementByPermutation([ perm, r0_portrait, r1_portrait ]) ], 0 ];
					fi;

					# If both r0/r1 portraits are in the form [word], 
					# check if the portrait we're about to return is an element of the nucleus
					if portrait_depth = 0 then
						nucleus_element := NucleusElementByPortrait([perm, r0_portrait, r1_portrait]);
						if not nucleus_element = fail then
							return [[nucleus_element], 0];
						fi;
					fi;
			
					return [ [ perm, r0_portrait, r1_portrait ], portrait_depth + 1 ]; 


				else
					# If g_i is odd
					if i = Size(g_list) then
						# If we make it through the whole list (i.e., fail on every g to recover r)
						return fail;
					fi;
				fi;
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
				contracting_depth := PortraitDepthUpperBound(r_len);
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