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
    Print("Size of perm group: ", Size(PermGroupOnLevel(G, level)), "\n");
    Print("Elements remaining: ", Size(ghConjugators), "\n");
    return Elements(ghConjugators);
end;

TestConjugacyRelationships := function(g, h, candidate_sigma_r, level)
    local sigma_g, cycle_structure, orbits, sizesWithMultipleCycles, size,
        relationsToPerms, dictKeys, RotateProduct, sigma_r, orbits_of_size,
        orbit, current_index, lhs, rhs, i, permsWithRelation, j, permsWithKey;

    sigma_g := PermOnLevel(g, level);
    cycle_structure := CycleStructurePerm(sigma_g);
    orbits := OrbitsPerms([sigma_g], [1..N_LETTERS]);
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
    while Length(candidate_sigma_r)  > 1 and i <= Length(dictKeys) do 
        lhs := Product(List(dictKeys[i][1], index -> Sections(g, level)[index]));
        rhs := Product(List(dictKeys[i][2], index -> Sections(h, level)[index]));
        Print("rhs: ", rhs, "lhs: ", lhs, "\n");
        if AreNotConjugateOnLevel(lhs, rhs, 2) then 
            permsWithRelation := LookupDictionary(relationsToPerms, dictKeys[i]);
            Print("Removing permutations ", permsWithRelation, "\n");
            SubtractSet(candidate_sigma_r, permsWithRelation);
            #looping backwards because we will remove elements of dictKeys
            for j in Reversed([i+1..Length(dictKeys)]) do 
                permsWithKey := LookupDictionary(relationsToPerms, dictKeys[i]);
                SubtractSet(permsWithKey, permsWithRelation);
                if Length(permsWithKey) = 0 then 
                    Remove(dictKeys, j);
                fi;
            od;
        fi;
        i := i + 1;
    od;
end;

recoveringL1 := function(g_t, h_t, max_level_to_try)
    local current_level, possibleRs, i, sigma_g, fixed_points;

    for current_level in [1..max_level_to_try] do 
        timeInHelper := 0;
        totalTime := 0;
        multiCycleTime := 0;
        orbitsOfSizeTime := 0;
        settingUpRelationTime := 0;
        Print("Attempting on level ", current_level, "\n");
        #Get possible sigma_r by looking at permutations that could conjugate all sigma_g/sigma_h pairs
        possibleRs := IntersectionOfConjugators(g_t, h_t, current_level);

        if Length(possibleRs) = 1 then
            return possibleRs[1];
        fi;
        if current_level < 6 then 
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
               TestConjugacyRelationships(g_t[i], h_t[i], possibleRs, current_level);
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

#recoveringL1 := function(g_t, h_t, max_level_to_try)
#    local current_level, sigma_r;
#
#    for current_level in [1..max_level_to_try] do
#        Print("Attempting on level ", current_level, "\n");
#        #Get possible sigma_r by looking at permutations that could conjugate all sigma_g/sigma_h pairs
#        Print("Working on intersection of conjugators...\n");
#        sigma_r := IntersectionOfConjugators(g_t, h_t, current_level);
#
#        if not (sigma_r = fail) then
#            Print("Succeeded on level ", current_level, "\n");
#            return [current_level, sigma_r];
#        fi;
#        #Narrow down possibilities for sigma_r by looking at conjugacy relationships between sections
#        #i := 1;
#        #Print("Testing conjugacy relations between sections\n");
#        #while i <= Length(g_t) and Length(possibleRs) > 1 do
#        #    sigma_g := PermOnLevel(g_t[i], current_level);            
#        #    fixed_points := [1..N_LETTERS];
#        #        if not IsOne(sigma_g) then
#        #            SubtractSet(fixed_points, MovedPoints(sigma_g));
#        #        fi;
#        #    if fixed_points > 1 or Maximum(CycleStructurePerm(sigma_g)) > 1 then 
#        #        possibleRs := TestConjugacyRelationships(g_t[i], h_t[i], possibleRs, current_level);
#        #    fi;
#        #    i := i + 1;
#        #od;
#        #if Length(possibleRs) = 1 then 
#        #    Print("Succeeded on level ", current_level, "\n");
#        #    return [current_level, possibleRs[1]];
#        #fi;
#    od;
#
#    Print("Failed.\n");
#    return fail;
#end;

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

gs := List([1..50], i -> RandomStabilizerIMGZ(3, 10, 10));
r := Product(List([1..50], i -> Random(G)));
hs := List(gs, g -> g^r);
recoveringL1(gs, hs, 10);
quit;