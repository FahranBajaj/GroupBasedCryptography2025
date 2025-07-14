LoadPackage("AutomGrp");
N_LETTERS := 2;
G := AutomatonGroup("a = (1, 1)(1, 2), b = (a, c), c = (b, 1)");
CONJUGATION_ACTION := OnPoints;

timeInHelper := 0;
totalTime := 0;
multiCycleTime := 0;
orbitsOfSizeTime := 0;
settingUpRelationTime := 0;
stabilizedLevels := 0;

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
    local sigma_g, sigma_h, ghConjugators, allConj, i, A, B, A_gens, imgs, phi, conj;

    # getting tuples of g and h values
    Print("\tSize of perm group: ", Size(PermGroupOnLevel(G, level)));
    if prev_conj <> [] then 
        A := PermGroupOnLevel(G,level);
        B := PermGroupOnLevel(G, level-1);
        A_gens := GeneratorsOfGroup(A);
        imgs := List(A_gens, a -> PermActionOnLevel(a,level,level-1,N_LETTERS));     
        phi := GroupHomomorphismByImagesNC(A, B, A_gens, imgs);
        ghConjugators := [];
        for conj in prev_conj do 
            ghConjugators := Union(ghConjugators, PreImages(phi, conj));
        od;
        Print("\tStarting size: ", Size(ghConjugators));
        i := 1;
    else 
        ghConjugators := FindAllConjugators(PermGroupOnLevel(G, level), PermOnLevel(g_t[1], level), PermOnLevel(h_t[1], level));
        i := 2;
    fi;
    while Size(ghConjugators) > 1 and i <= Length(g_t) do
        # all conjugators of a g/h pair
        sigma_g := PermOnLevel(g_t[i], level);
        sigma_h := PermOnLevel(h_t[i], level);
        allConj := FindAllConjugators(PermGroupOnLevel(G, level), sigma_g, sigma_h);
        ghConjugators := Intersection(ghConjugators, allConj);
        i := i + 1;
    od;

    if Size(ghConjugators) = 1 then 
        Print("\tSingle element left after intersection of conjugators\n");
        return ghConjugators[1];
    fi;

    Print("\tElements remaining: ", Size(ghConjugators), "\n");
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
    Sort(valid_sigma_r);
    while Length(valid_sigma_r)  > 1 and i <= Length(dictKeys) do 
        lhs := Product(List(dictKeys[i][1], index -> Sections(g, level)[index]));
        rhs := Product(List(dictKeys[i][2], index -> Sections(h, level)[index]));
        if AreNotConjugateOnLevel(lhs, rhs, 2) then 
            permsWithRelation := LookupDictionary(relationsToPerms, dictKeys[i]);
            SubtractSet(valid_sigma_r, permsWithRelation);
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
    return valid_sigma_r;
end;
    

recoveringL1 := function(g_t, h_t, currentLevelOfAttack)
    local UniqueOnLevel, current_level, possibleRs, i, sigma_g, possiblePreviousLevel, 
    fixed_points, level, A, B, A_gens, imgs, phi;
    
    UniqueOnLevel := function(possibleRs, bigLevel, smallLevel)
        local firstAction, i;

        firstAction := PermActionOnLevel(possibleRs[1], bigLevel, smallLevel, 2);
        i := 2;
        while i <= Length(possibleRs) do 
            if PermActionOnLevel(possibleRs[i], bigLevel, smallLevel, 2) <> firstAction then 
                return false;
            fi;
            i := i + 1;
        od;
        return true;
    end;

    possiblePreviousLevel := [];
    for current_level in [Maximum(1, stabilizedLevels - currentLevelOfAttack)..Maximum(1, stabilizedLevels - currentLevelOfAttack) + 4] do 
        Print("Attempting to recover the action ", current_level, " levels down\n");
        #Get possible sigma_r by looking at permutations that could conjugate all sigma_g/sigma_h pairs
        #This is only useful if we are on a deep enough level that permutations will be nontrivial
        if current_level >= stabilizedLevels - currentLevelOfAttack + 2 then 
            possibleRs := IntersectionOfConjugators(g_t, h_t, current_level, possiblePreviousLevel);
        else 
            if possiblePreviousLevel <> [] then 
                A := PermGroupOnLevel(G, current_level);
                B := PermGroupOnLevel(G, current_level - 1);
                A_gens := GeneratorsOfGroup(A);
                imgs := List(A_gens, a -> PermActionOnLevel(a, current_level, current_level - 1,N_LETTERS));     
                phi := GroupHomomorphismByImagesNC(A, B, A_gens, imgs);
                possibleRs := Concatenation(List(possiblePreviousLevel, perm -> Elements(PreImages(phi, perm))));
            else
                possibleRs := Elements(PermGroupOnLevel(G, current_level));
            fi;
        fi;
        Print("\tFinished or skipped intersection of conjugators. There are ", Length(possibleRs), " remaining permutations\n");
        #this if statement will usually be false so may as well check it before
        #looping through levels in reversed order
        if UniqueOnLevel(possibleRs, current_level, 1) then
            for level in Reversed([2..current_level]) do 
                if UniqueOnLevel(possibleRs, current_level, level) then 
                    return [level, PermActionOnLevel(possibleRs[1], current_level, level, 2)];
                fi;
            od;
            return [1, PermActionOnLevel(possibleRs[1], current_level, 1, 2)];
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
                Print("\tAfter a round of testing conjugacy relationships, ", Length(possibleRs), " permutations remain.\n");
            fi;
            i := i + 1;
            #Print("Elems remaining after a round of conjugacy relations: ", Length(possibleRs), "\n");
        od;
        #Print("Sigma_r remaining: ", possibleRs, "\n");
        if UniqueOnLevel(possibleRs, current_level, 1) then
            for level in Reversed([2..current_level]) do 
                if UniqueOnLevel(possibleRs, current_level, level) then 
                    return [level, PermActionOnLevel(possibleRs[1], current_level, level, 2)];
                fi;
            od;
            return [1, PermActionOnLevel(possibleRs[1], current_level, 1, 2)];
        fi;
        possiblePreviousLevel := possibleRs;
    od;
    Print("Failed to recover action within several levels\n");
    return fail;
end;

#Reset(GlobalMersenneTwister,CurrentDateTimeString()); #new random seed
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

stabilizedLevels := 4;
gs := List([1..5], i -> RandomStabilizerIMGZ(stabilizedLevels - 1, 10, 10));
r := Product(List([1..50], i -> Random(G)));
hs := List(gs, g -> g^r);
recoveringL1(gs, hs, 1);
