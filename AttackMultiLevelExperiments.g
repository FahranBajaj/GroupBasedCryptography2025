LoadPackage("AutomGrp");
N_LETTERS := 2;
G := AutomatonGroup("a = (1, 1)(1, 2), b = (a, c), c = (b, 1)");
CONJUGATION_ACTION := OnPoints;
Reset(GlobalMersenneTwister,CurrentDateTimeString()); #new random seed

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

recoveringL1 := function(g_t, h_t, min_level_to_try, max_level_to_try)
    local possibleRsFirstLevel, current_level, possibleRs, i, sigma_g, 
    fixed_points, firstLevelRs;

    possibleRsFirstLevel := function(possibleRs, level)
        local firstLevelActions, i;
        firstLevelActions := List(possibleRs, sigma_r -> PermActionOnLevel(sigma_r, level, 1, N_LETTERS));
        Sort(firstLevelActions);
        i := 1;
        while i < Length(firstLevelActions) do 
            if firstLevelActions[i] = firstLevelActions[i + 1] then 
                Remove(firstLevelActions, i);
            else 
                i := i + 1;
            fi;
        od;
        return firstLevelActions;
    end;

    for current_level in [min_level_to_try..max_level_to_try] do 
        Print("Attempting on level ", current_level, "\n");
        #Get possible sigma_r by looking at permutations that could conjugate all sigma_g/sigma_h pairs
        possibleRs := IntersectionOfConjugators(g_t, h_t, current_level);
        Print("Size of perm group on level ", current_level, ": ", Size(PermGroupOnLevel(G, current_level)), "\n");
        Print("Elements remaining after intersection of conjugators: ", Length(possibleRs), "\n");
        firstLevelRs := possibleRsFirstLevel(possibleRs, current_level);
        if Length(firstLevelRs) = 1 then
            return firstLevelRs[1];
        fi;
        #if current_level < 6 then 
        #    continue;
        #fi;
        #Narrow down possibilities for sigma_r by looking at conjugacy relationships between sections
        i := 1;
        while i <= Length(g_t) and Length(firstLevelRs) > 1 do
            sigma_g := PermOnLevel(g_t[i], current_level);            
            fixed_points := [1..N_LETTERS^current_level];
                if not IsOne(sigma_g) then
                    SubtractSet(fixed_points, MovedPoints(sigma_g));
                fi;
            if fixed_points > 1 or Maximum(CycleStructurePerm(sigma_g)) > 1 then 
               possibleRs := TestConjugacyRelationships(g_t[i], h_t[i], possibleRs, current_level);
               firstLevelRs := possibleRsFirstLevel(possibleRs, current_level);
            fi;
            i := i + 1;
            Print("Elems remaining after a round of conjugacy relations: ", Length(possibleRs), "\n");
        od;
        Print("Sigma_r remaining: ", possibleRs, "\n");
        if Length(firstLevelRs) = 1 then 
            #Print("Succeeded on level ", current_level, "\n");
            return firstLevelRs[1];
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

#gs := List([1..30], i -> RandomStabilizerIMGZ(3, 10, 10));
#r := RandomElement(10, G);
#hs := List(gs, g -> g^r);
#recoveringL1(gs, hs, 3, 10);

PermActionAtVertex := function(perm, bigLevel, vertex)
    local topLevelAction, permSplitLeftRight, topLevelSwap, singleSubtreePerm, permAsList, i, nextVertex;

    topLevelAction := PermActionOnLevel(perm, bigLevel, 1, 2);
    if vertex = [] then 
        return topLevelAction;
    fi;
    if topLevelAction = () then 
        permSplitLeftRight := perm;
    else 
        topLevelSwap := PermList(Concatenation([2^(bigLevel - 1) + 1..2^bigLevel], [1..2^(bigLevel-1)]));
        permSplitLeftRight := perm * topLevelSwap;
    fi;
    if vertex[1] = 0 then 
        singleSubtreePerm := RestrictedPermNC(permSplitLeftRight, [1..2^(bigLevel - 1)]);
    else 
        permAsList := ListPerm(permSplitLeftRight, 2^(bigLevel));
        for i in [1..2^(bigLevel - 1)] do 
            Remove(permAsList, 1);
        od;
        singleSubtreePerm := PermList(List([1..2^(bigLevel - 1)], i -> permAsList[i] - 2^(bigLevel - 1)));
    fi;

    nextVertex := ShallowCopy(vertex);
    Remove(nextVertex, 1);
    return PermActionAtVertex(singleSubtreePerm, bigLevel - 1, nextVertex);
end;