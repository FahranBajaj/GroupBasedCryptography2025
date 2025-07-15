LoadPackage("AutomGrp");

RandomElementList := function(len, group, list_size)
	local element_list, generators, i, prod, j;

    element_list := [];
    generators := GeneratorsOfGroup(group);

   	for i in [1..list_size] do
		prod := One(group);
		for j in [1..len] do
			prod := prod * Random(generators);
		od;
		Append(element_list, [prod]);
	od;
	return element_list;
end;

#-----------Part 1: Read Groups into File-----------
# DEGREES := [3, 7, 12, 20];
# NUM_GENERATORS := [3, 7, 10];
# PROPORTIONS := ["0.3", "0.7", "0.9"];
# groupsToTestFile := OutputTextFile("./ContractingGroupsFound/GroupsToTestAttack.g", true);
# listOfGroups := "groupsToTest := [";

# for degree in DEGREES do
#     for num_generators in NUM_GENERATORS do 
#         for proportionString in PROPORTIONS do 
#             if degree = 3 and num_generators = 10 and proportionString = "0.9" then 
#                 continue;
#             fi;
#             filePath := Concatenation("./ContractingGroupsFound/", String(degree), "_", String(num_generators), "_", proportionString, "(2).g");
#             Read(filePath);
#             numWritten := 0;
#             for groupRec in groupsFound do 
#                 if IsBound(groupRec.finite) and not groupRec.finite then 
#                     numWritten := numWritten + 1;
#                     groupNameString := Concatenation("G_", String(degree), "_", String(num_generators), "_", proportionString{[1, 3]}, "_", String(numWritten));
#                     AppendTo("./ContractingGroupsFound/GroupsToTestAttack.g", groupNameString, " := ", groupRec, ";\n");
#                     listOfGroups := Concatenation(listOfGroups, groupNameString, ", ");
#                     if numWritten = 3 then 
#                         break;
#                     fi;
#                 fi;
#             od;  
#         od;
#     od;
# od;     

# listOfGroups := Concatenation(listOfGroups, "];\n");
# AppendTo("./ContractingGroupsFound/GroupsToTestAttack.g", listOfGroups);
# CloseStream(groupsToTestFile);

#-----------Part 2: Check if Portrait is Easy to Compute-----------

# Read("./ContractingGroupsFound/GroupsToTestAttack.g");
# groupsToTestFile := OutputTextFile("./ContractingGroupsFound/GroupsToTestAttack.g", true);

# TestParameterFeasibility := function(G, length)
#     local ComputePortraits, elems, result, NUM_SAMPLES, TIME_PER_SAMPLE;
# 	NUM_SAMPLES := 30;
# 	TIME_PER_SAMPLE := 20;
#     ComputePortraits := function(elems)
#         local elem, portrait;
#         for elem in elems do 
#             portrait := AutomPortrait(elem);
#         od;
#     end;

#     elems := RandomElementList(length, G, NUM_SAMPLES);
#     result := IO_CallWithTimeout(rec(seconds := NUM_SAMPLES * TIME_PER_SAMPLE), ComputePortraits, elems);
#     return result[1];
# end;

# GROUPS_TO_TEST := [G_20_10_09_2, G_20_10_09_3];
# GROUP_STRINGS := ["G_20_10_09_2", "G_20_10_09_3"];
# LENGTHS := [10, 100];

# for i in [1..Length(GROUPS_TO_TEST)] do 
#     for length in LENGTHS do 
#         group := AutomatonGroup(GROUPS_TO_TEST[i].automaton);
#         AppendTo("./ContractingGroupsFound/GroupsToTestAttack.g", "AddDictionary(feasibilities, [", GROUP_STRINGS[i], ", ", length, "], ", TestParameterFeasibility(group, length), ");\n");
#     od;
# od;
# CloseStream(groupsToTestFile);

#-----------Part 3: Compute Portrait Depth Approximation-----------
GetStatisticalDepthBound := function(group, length)
    local ALPHA, N, EPSILON_1, EPSILON_2, ValueCounts, ContractingDepths, 
        pdf, values, counts, sum, i, time;
    ALPHA := 0.05;
    N := 2000;
    EPSILON_1 := 0.0065;
    EPSILON_2 := 0.04;

    time := Runtime();
    ValueCounts := function(list)
        local distinctValues, counts, i, prevValue;
        distinctValues := [];
        counts := NewDictionary(1, true);
        for i in list do 
                if KnowsDictionary(counts, i) then 
                        prevValue := LookupDictionary(counts, i);
                        prevValue := prevValue + 1;
                        AddDictionary(counts, i, prevValue);
                else 
                        Append(distinctValues, [i]);
                        AddDictionary(counts, i, 1);
                fi;
        od;
        Sort(distinctValues);
        return [distinctValues, counts];
    end;

    ContractingDepths := List(RandomElementList(length, group, N), elem -> AutomPortraitDepth(elem));
    Print(ContractingDepths);
    pdf := ValueCounts(ContractingDepths);
    values := pdf[1];
    counts := pdf[2];
    sum := LookupDictionary(counts, values[1]);
    i := 1;
    while sum < Int(Ceil(N*(1-EPSILON_1))) do 
        i := i + 1;
        sum := sum + LookupDictionary(counts, values[i]);
    od;

    return [values[i], Runtime() - time];
end;

Read("./ContractingGroupsFound/GroupsToTestAttack.g");
groupsToTestFile := OutputTextFile("./ContractingGroupsFound/GroupsToTestAttack.g", true);
GROUPS_TO_BOUND := [];
GROUP_STRINGS := [];
LENGTHS := [10, 100];

for i in [1..GROUPS_TO_BOUND] do 
    group := AutomatonGroup(GROUPS_TO_BOUND[i].automaton);
    for length in LENGTHS do 
        if LookupDictionary (feasibilities, [GROUPS_TO_BOUND[i], length]) then 
            boundAndTime := GetStatisticalDepthBound(group, length)
            bound := boundAndTime[1];
            time := boundAndTime[2];
            AppendTo("./ContractingGroupsFound/GroupsToTestAttack.g", "AddDictionary(depthBounds, [", GROUP_STRINGS[i], ", ", length, "], ", bound, ");\n");
            AppendTo("./ContractingGroupsFound/GroupsToTestAttack.g", "AddDictionary(depthTimes, [", GROUP_STRINGS[i], ", ", length, "], ", time, ");\n");
        fi;
    od;
od;
CloseStream(groupsToTestFile);