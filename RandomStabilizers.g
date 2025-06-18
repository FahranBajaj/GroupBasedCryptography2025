LoadPackage("AutomGrp");
Reset(GlobalMersenneTwister, CurrentDateTimeString());

#Returns a random element of the subgroup over which the Grigorchuk group is branching
RandomSubgroupElementGrigorchuk := function()
    local G, g, num_repetitions;
    G := AutomatonGroup("a = (1, 1)(1, 2), b = (a, c), c = (a, d), d = (1, b)");
    g := Random(G);
    num_repetitions := Random([-10..10]);
    return g^-1 * (a*b)^(2*num_repetitions) * g;
end;

#Returns an element that stabilizes the nth level, given a method that generates
#random elements of the subgroup over which G is branching
RandomStabilizerNthLevel := function(level, RandomSubgroupElement, degree)
    if level = 0 then 
        return RandomSubgroupElement();
    fi;

    return TreeAutomorphism(List([1..degree], i -> RandomStabilizerNthLevel(level - 1, RandomSubgroupElement, degree)), ());
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

RandomWordInGenerators := function(len, num_generators)
    local choicesOfGenerators;
    choicesOfGenerators := List([1..len], i -> Random([1..num_generators]));
    return choicesOfGenerators;
    
    #wordFunction := function(generators)
    #    factors := [];
    #    for i in [1..len] do
    #        if inverses[i] then 
    #            factor := generators[choicesOfGenerators[i]]^-1;
    #        else 
    #            factor := generators[choicesOfGenerators[i]];
    #        fi;
    #    od;
    #    return Product(factors);
    #end;
    #return wordFunction;
end;

G := AutomatonGroup("a = (1, 1)(1, 2), b = (a, c), c = (b, 1)");
CONJUGATOR_LIFTING_DICTIONARY := NewDictionary([1, 1], true);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [1, 1], [2]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [2, 1], [3]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [3, 1], [1, 2, 1]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [1, 2], [1, 2, 1]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [2, 2], [1, 3, 1]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [3, 2], [2]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [0, 1], [0]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [0, 2], [0]);


NextLevelConjugator := function(wordOfElement, sectionNumber)
    local newGeneratorIndices, i;
    newGeneratorIndices := [];

    for i in wordOfElement do 
        Append(newGeneratorIndices, LookupDictionary(CONJUGATOR_LIFTING_DICTIONARY, [i, sectionNumber]));
    od;
    return newGeneratorIndices;
end;

ProductOfPieces := function(pieces)
    local product, piece, conjugatorWord, conjugator, generator, commutatorWord,
         commutator;
    product := One(G);
    for piece in pieces do 
        conjugatorWord := piece[1];
        conjugator := One(G);
        for generator in conjugatorWord do
            if generator = 0 then
                conjugator := conjugator * One(G);
            elif generator = 1 then 
                conjugator := conjugator * a;
            elif generator = 2 then 
                conjugator := conjugator * b;
            else
                conjugator := conjugator * c;
            fi;
        od;
        product := product*conjugator^-1;
        commutatorWord := piece[2];
        for commutator in commutatorWord do 
            if commutator = 0 then
                product := product * One(G);
            elif commutator = 1 then 
                product := product * (a*b)^2;
            else 
                product := product * (b*c)^2;
            fi;
        od;
        product := product * conjugator;
    od;
    return product;
end;

#Computes random stabilizers of the nth level for the iterated monodromy
#group for z^2 + i
RandomStabilizerIMGZ := function(level, innerWordLength, conjugatorLength)
    local current_level, stabilizers_of_level, i, conjugator, innerWord, stabilizers_of_next_level,
        pointer, pieces_of_next_stabilizer, section1, piece, newConjugator, 
        commutator, section2;
    current_level := 0;
    stabilizers_of_level := [];
    for i in [1..2^level] do 
        if i = 1 then
            conjugator := RandomWordInGenerators(conjugatorLength, 3);
            innerWord := RandomWordInGenerators(innerWordLength, 2);
            Append(stabilizers_of_level, [[[conjugator, innerWord]]]);
        else
            Append(stabilizers_of_level, [[[[0],[0]]]]);
        fi;
    od;

    while current_level < level do 
        stabilizers_of_next_level := [];
        pointer := 1;
        while pointer < Length(stabilizers_of_level) do 
            pieces_of_next_stabilizer := [];
            section1 := stabilizers_of_level[pointer];
            for piece in section1 do 
                newConjugator := NextLevelConjugator(piece[1], 1);

                for commutator in piece[2] do
                    if commutator = 0 then
                        Append(pieces_of_next_stabilizer, [[newConjugator, [0]]]);
                    elif commutator = 1 then 
                        Append(pieces_of_next_stabilizer, [[newConjugator, [2]]]);
                    else 
                        Append(pieces_of_next_stabilizer, [[Concatenation([1, 2, 3], newConjugator), [1]]]);
                        Append(pieces_of_next_stabilizer, [[Concatenation([2], newConjugator), [2]]]);
                        Append(pieces_of_next_stabilizer, [[Concatenation([1], newConjugator), [1]]]);
                    fi;
                od;
            od;
            pointer := pointer + 1;
            section2 := stabilizers_of_level[pointer];
            for piece in section2 do 
                newConjugator := NextLevelConjugator(piece[1], 2);
                for commutator in piece[2] do 
                    if commutator = 0 then
                        Append(pieces_of_next_stabilizer, [[newConjugator, [0]]]);
                    elif commutator = 1 then 
                        Append(pieces_of_next_stabilizer, [[Concatenation([1], newConjugator), [2]]]);
                    else 
                        Append(pieces_of_next_stabilizer, [[Concatenation([1, 2, 3], [1], newConjugator), [1]]]);
                        Append(pieces_of_next_stabilizer, [[Concatenation([2], [1], newConjugator), [2]]]);
                        Append(pieces_of_next_stabilizer, [[Concatenation([1], [1], newConjugator), [1]]]);
                    fi;
                od;
            od;
            Append(stabilizers_of_next_level, [pieces_of_next_stabilizer]);
            pointer := pointer + 1;
        od;
        current_level := current_level + 1;
        stabilizers_of_level := stabilizers_of_next_level;
        stabilizers_of_next_level := [];
    od;
    return ProductOfPieces(stabilizers_of_level[1]);
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

treeAut := RandomStabilizerIMGZ(4,5,4);
