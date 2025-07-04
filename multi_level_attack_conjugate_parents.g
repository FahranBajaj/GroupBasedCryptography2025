LoadPackage("AutomGrp");
N_LETTERS := 2;
G := AutomatonGroup("a = (1, 1)(1, 2), b = (a, c), c = (b, 1)");
CONJUGATION_ACTION := OnPoints;

timeInHelper := 0;
totalTime := 0;
multiCycleTime := 0;
orbitsOfSizeTime := 0;
settingUpRelationTime := 0;


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

IntersectionOfConjugators := function(g_t, h_t, level, prev_conj)
    local sigma_g, sigma_h, ghConjugators, allConj, i, A, B, A_gens, imgs, phi, ker, r_c, r_c_list, r_c_reps, possible_conj_cosets, rep;

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

    # try to narrow down what's left by using previous level!
    if level > 1 then
        # homomorphism from P_n to P_(n-1): child to parent
        A := PermGroupOnLevel(G,level);
        B := PermGroupOnLevel(G, level-1);

        A_gens := GeneratorsOfGroup(A);
        imgs := List(A_gens, a -> PermActionOnLevel(a,level,level-1,2));        # change to general deg of tree

        phi := GroupHomomorphismByImages(A, B, A_gens, imgs);


        # Take P_n/ker(f) and consider one rep from each coset
        ker := Kernel(phi);
        r_c := RightCosets(A,ker);
        r_c_list := Elements(r_c);      # might not want to do this for time?
        r_c_reps := List(r_c_list, rc -> Representative(rc));

        # if the image of the rep is in old allConj, keep the coset
        possible_conj_cosets := [];  # the keepers

        for i in [1..Length(r_c_reps)] do
            if phi(r_c_reps[i]) in prev_conj then
                Append(possible_conj_cosets, Elements(r_c_list[i]));
            fi;
        od;

        ghConjugators := Intersection(ghConjugators,possible_conj_cosets);
    fi;
    
    Print("Size of perm group: ", Size(PermGroupOnLevel(G, level)), "\n");
    Print("Elements remaining: ", Size(ghConjugators), "\n");
    return Elements(ghConjugators);
end;

#Helper method to recover action of r on the first level. Takes one (g, h) pair and 
#possible sigma_r and tests the conjugacy relationships given by each sigma_r
TestConjugacyRelationships := function(g, h, candidate_sigma_r, level)
    local sigma_g, cycle_structure, orbits, sizesWithMultipleCycles, 
    fixed_points, size, orbits_of_size, valid_sigma_r, sigma_r, valid, 
    orbit, lhs, rhs, current_index, section, arentConj;

    totalTime := totalTime - Runtime();
    multiCycleTime := multiCycleTime - Runtime();

    sigma_g := PermOnLevel(g, level);
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
    multiCycleTime := multiCycleTime + Runtime();
    valid_sigma_r := [];
    for sigma_r in candidate_sigma_r do
        valid := true;
        for size in sizesWithMultipleCycles do
            orbitsOfSizeTime := orbitsOfSizeTime - Runtime();
            if size = 1 then 
                orbits_of_size := List(fixed_points, pt -> [pt]);
            else 
                orbits_of_size := Filtered(orbits, orbit -> Length(orbit) = size);
            fi;
            orbitsOfSizeTime := orbitsOfSizeTime + Runtime();
            for orbit in orbits_of_size do
                #g_{a_1}g_{a_2}...g_{a_n} ~ h_{b_1}h_{b_2}...h_{b_n}
                settingUpRelationTime := settingUpRelationTime - Runtime();
                lhs := One(G); 
                rhs := One(G);
                current_index := orbit[1];

                for section in [1..size] do 
                    lhs := lhs * Sections(g, level)[current_index];
                    rhs := rhs * Sections(h, level)[current_index^sigma_r]; # start with only one cycle then go on from there

                    current_index := current_index^sigma_g;

                od;

                settingUpRelationTime := settingUpRelationTime + Runtime();
                timeInHelper := timeInHelper - Runtime();
                arentConj := AreNotConjugateOnLevel(lhs, rhs, 2);
                timeInHelper := timeInHelper + Runtime();
                if arentConj then
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
    totalTime := totalTime + Runtime();
    return valid_sigma_r;
end;

recoveringL1 := function(g_t, h_t, max_level_to_try)
    local current_level, possibleRs, i, sigma_g, fixed_points, previous_conjs;

    previous_conjs := [];   # me

    for current_level in [1..max_level_to_try] do 
        timeInHelper := 0;
        totalTime := 0;
        multiCycleTime := 0;
        orbitsOfSizeTime := 0;
        settingUpRelationTime := 0;
        Print("Attempting on level ", current_level, "\n");

        #Get possible sigma_r by looking at permutations that could conjugate all sigma_g/sigma_h pairs
        possibleRs := IntersectionOfConjugators(g_t, h_t, current_level, previous_conjs);

        previous_conjs := possibleRs;

        if Length(possibleRs) = 1 then
            return possibleRs[1];
        fi;
        if current_level < max_level_to_try then 
            continue;
        fi;

        #Narrow down possibilities for sigma_r by looking at conjugacy relationships between sections
        i := 1;
        while i <= Length(g_t) and Length(possibleRs) > 1 do
            sigma_g := PermOnLevel(g_t[i], current_level);            
            fixed_points := [1..N_LETTERS^current_level];
                if not IsOne(sigma_g) then
                    SubtractSet(fixed_points, MovedPoints(sigma_g));
                fi;
            if fixed_points > 1 or Maximum(CycleStructurePerm(sigma_g)) > 1 then 
                possibleRs := TestConjugacyRelationships(g_t[i], h_t[i], possibleRs, current_level);
            fi;
            i := i + 1;
            Print("Elems remaining after a round of conjugacy relations: ", Length(possibleRs), "\n");
        od;
        Print("Time in helper: ", timeInHelper, "\n");
        Print("Total time: ", totalTime, "\n");
        Print("Multiple cycle time: ", multiCycleTime, "\n");
        Print("Orbits of size time: ", orbitsOfSizeTime, "\n");
        Print("Setting up relations time: ", settingUpRelationTime, "\n");
        if Length(possibleRs) = 1 then 
            Print("Succeeded on level ", current_level, "\n");
            return possibleRs[1];
        fi;
    od;
    Print("Failed.\n");
    return fail;
end;

Reset(GlobalMersenneTwister,CurrentDateTimeString()); #new random seed
RandomWordInGenerators := function(len, num_generators)
    local choicesOfGenerators;
    choicesOfGenerators := List([1..len], i -> Random([1..num_generators]));
    return choicesOfGenerators;
end;

#Self-replicating equations:
#b = (a, c), c = (b, 1), aba = (c, a), aca = (1, b)
CONJUGATOR_LIFTING_DICTIONARY := NewDictionary(1, true);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, 1, [2]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, 2, [3]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, 3, [1, 2, 1]);

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
            elif generator = 2 then 
                conjugator := conjugator * b;
            else
                conjugator := conjugator * c;
            fi;
        od;
        product := product*conjugator^-1;
        commutator := piece[1];
		if commutator = 1 then 
			product := product * (a*b)^2;
		else 
			product := product * (b*c)^2;
		fi;
        product := product * conjugator;
    od;
    return product;
end;

#Computes random stabilizers of the nth level for the iterated monodromy
#group for z^2 + i. All sections at nth level are identity except first one.

#Lifting equations: [b, c] = ([a, b], 1), 
#[a, b]^{abc}[b, c]^b[a, b]^a = [c, b^a] = ([b, c], 1)
RandomStabilizerIMGZMostlyId := function(level, innerWordLength, conjugatorLength)
	local current_level, current_element, lifted_element, piece, newConjugator,
		commutator;
	current_level := 0;
	#Represent an element of N by list of [generator, conjugator] factors
	#Where each conjugator is a list of numbers representing generators
	current_element := List([1..innerWordLength], i -> [Random([1..2]), RandomWordInGenerators(conjugatorLength, 3)]);
	while current_level < level do 
		lifted_element := [];
		for piece in current_element do 
			#piece = [generator, conjugator]
			newConjugator := NextLevelConjugator(piece[2]);
			commutator := piece[1];
			if commutator = 1 then 
            	Append(lifted_element, [[2, newConjugator]]);
			else 
				Append(lifted_element, [[1, Concatenation([1, 2, 3], newConjugator)]]);
				Append(lifted_element, [[2, Concatenation([2], newConjugator)]]);
				Append(lifted_element, [[1, Concatenation([1], newConjugator)]]);
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

RandomStabilizerIMGZ := function(level, innerWordLength, conjugatorLength)
    local liftedSections, product, conjugator, i;
    liftedSections := List([1..2^level], i -> RandomStabilizerIMGZMostlyId(level, innerWordLength, conjugatorLength));
    product := liftedSections[1];
    for i in [2..2^level] do
        conjugator := ElemMappingAToBOnLevel(G, 1, i, level);
        product := product * liftedSections[i]^conjugator;
    od;
    return product;
end;

gs := List([1..50], i -> RandomStabilizerIMGZ(2, 10, 10));
r := Product(List([1..50], i -> Random(G)));
hs := List(gs, g -> g^r);
recoveringL1(gs, hs, 4);
