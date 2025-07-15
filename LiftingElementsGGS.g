LoadPackage("AutomGrp");
Reset(GlobalMersenneTwister, CurrentDateTimeString());

new_GGS_gr := function(v)
    # v: defining vector. v[0] <> 1 and v[Length(v)] = 1.
    # Length(v) = degree - 1

    local degree, gen_details, current_gen, i, placeholder, possible_gens, gen_names, currentGGS;

    # degree of tree
    degree := Length(v) + 1;

    gen_details := [];

    # adding 1
    current_gen := List([1..degree], i -> 1);
    Append(current_gen, [()]);
    Append(gen_details, [current_gen]);
    
    # adding a
    current_gen := List([1..degree], i -> 1);
    Append(current_gen, [CycleFromList([1..degree])]);
    Append(gen_details, [current_gen]);

    # now making all of the "bonus" generators (a to a power)
    for i in v do 
        if i <> 0 and i <> 1 then 
            current_gen := List([1..degree], i -> 1);
            Append(current_gen, [CycleFromList([1..degree])^i]);
            Append(gen_details, [current_gen]);
        fi;
    od;

    # making b
    current_gen := [];
    placeholder := 4;

    for i in [1..Length(v)] do 
        if v[i] = 0 then
            Append(current_gen, [1]);
        elif v[i] = 1 then 
            Append(current_gen, [2]);
        else
            Append(current_gen, [placeholder]);
            placeholder := placeholder + 1;
        fi;
    od;

    Append(current_gen, [2]);   # adding a at the end
    Append(current_gen, [()]);
    
    gen_details := Concatenation(gen_details{[1,2]}, [current_gen], gen_details{[3..Length(gen_details)]});
    
    possible_gens := ["1", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t"];
    gen_names := List([1..Length(gen_details)], i -> possible_gens[i]);

    # new automaton group!
    currentGGS := AutomatonGroup(gen_details, gen_names);

    return Subgroup(currentGGS, [a,b]); # so we don't use all the extra variables
end;

#Returns a random element of the subgroup over which a GGS group with defining vector v is branching
RandomSubgroupElementGGS := function(G)
    local ab_sg, g, num_repetitions;
    g := Random(G);
    num_repetitions := Random([-10..10]);
    return g^-1 * (a^-1*b^-1*a*b)^(num_repetitions) * g;
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

Reset(GlobalMersenneTwister,CurrentDateTimeString()); #new random seed

RandomWordInGenerators := function(len, num_generators)
    local choicesOfGenerators;
    choicesOfGenerators := List([1..len], i -> Random([1..num_generators]));
    return choicesOfGenerators;
end;

v := [1,1,0,0];
G := new_GGS_gr(v);

#Self-replicating equations:

d := Length(v) + 1;
power := v[1];
for j in [1..d] do
    power := power * j;
    
    if power mod d = 1 then 
        lift_power := j;
        break;
    fi;
od;

CONJUGATOR_LIFTING_DICTIONARY := NewDictionary(1, true);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, 1, List([1..lift_power], i -> 2));
b_lift := List([1..(d-1)], i -> 1);
Append(b_lift, [2,1]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, 2, b_lift);

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
            else
                conjugator := conjugator * b;
            fi;
        od;

        product := product*conjugator^-1;
        commutator := piece[1];
		if commutator = 1 then 
			product := product * (a^-1*b^-1*a*b);
        else
            product := product * (b^-1*a^-1*b*a);
        fi;

        product := product * conjugator;
    od;
    return product;
end;

#Computes random stabilizers of the nth level for the GGS group with vector v. 
#All sections at nth level are identity except first one.

#Lifting equations: 
    # [b,b^a] = [a,b]^b * [b,a] = ([a,b],1,...,1)
    # [b,b^a]^-1 = [a,b] * [b,a]^b = ([b,a],1,...,1)
RandomStabilizerGGSMostlyId := function(level, innerWordLength, conjugatorLength)
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
                Append(lifted_element, [[1, Concatenation([b], newConjugator)]]);
                Append(lifted_element, [[2, newConjugator]]);
			else 
                Append(lifted_element, [[1, newConjugator]]);
                Append(lifted_element, [[2, Concatenation([b], newConjugator)]]);
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

RandomStabilizerGGS := function(level, degree, innerWordLength, conjugatorLength)
    local liftedSections, product, conjugator, i;
    liftedSections := List([1..degree^level], i -> RandomStabilizerIMGZMostlyId(level, innerWordLength, conjugatorLength));
    product := liftedSections[1];
    for i in [2..degree^level] do
        conjugator := ElemMappingAToBOnLevel(G, 1, i, level);
        product := product * liftedSections[i]^conjugator;
    od;
    return product;
end;