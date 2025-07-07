# G := AutomatonGroup("a = (b, 1, 1)(1,3,2), b = (1, c, 1)(1,3), c = (b, d, 1)(2,3), d = (1, 1, 1)(2,3)");
# p1 :=[ (2,3), [ b^2 ], [ 1 ], [ (), [(), [ b ], [ d ], [ 1 ] ], [(1,3), [(),[b],[b],[d]]], [ 1 ] ] ];
# p2 :=[ (2,3), [ b^2 ], [ 1 ], [ (), [(), [ b ], [ d ], [ 1 ]], [(1,3), [(),[b],[b],[d]]], [ 1 ] ] ];

# p1 :=[ (2,3), [ b^2 ], [ 1 ], [ (), [c], [(1,3), [(),[b],[b],[d]]], [ 1 ] ] ];
# p2 :=[ (2,3), [ b^2 ], [ 1 ], [ (), [(), [ b ], [ d ], [ 1 ]], [(1,3), [(),[b],[b],[d]]], [ 1 ] ] ];

# p1 := [ (2,3), [ b ], [ 1 ], [ c ] ];
# p2 := [(2,3), [b], [1], [(2,3), [b], [d], [1]]];

G := AutomatonGroup("a = (1, 1)(1, 2), b = (a, c), c = (b, 1)");
r := c*a*(b*c)^2*a*b*a;


p1 := AutomPortrait(r);
p2 := [ (1,2), [ (1,2), [ a ], [ c ] ], [ (), [ (1,2), [ (), [ (1,2), [ c ], [ a ] ],  [ (), [ (), [ a ], [ (), [ (), [ a ], [ 1 ] ], [ 1 ] ] ], [ 1 ] ] ], [ a ] ], [ (1,2), [ 1 ], [ (), [ a ], [ (), [ (), [ a ], [ (), [ (), [ a ], [ 1 ] ], [ 1 ] ] ], [ 1 ] ] ] ] ] ];


comparing_portraits := function(short_port, long_port)
    local answer, sections, level, comparing_portraits_recursive;
    answer := true;
    sections := [];
    level := 1;

    comparing_portraits_recursive := function(short_port, long_port, level, answer, sections)
        # short_port: AutomPortrait(r), long_port: the r we build, level: must start with 1

        local equality_check, i, current_section, tf, section_nums;

        if answer = false then
            return false;
        fi;

        section_nums := sections;

        tf := answer;

        if Length(short_port) = 1 and Length(long_port) = 1 then # both in (quasi)nucleus
            equality_check := (short_port[1] = long_port[1]);

            if equality_check = false then      # CAN'T COMPARE 1S
                if short_port[1] = One(G) and long_port[1] = 1 then
                    equality_check := true;
                elif short_port[1] = 1 and long_port[1] = One(G) then
                    equality_check := true;
                elif short_port[1] = One(G) and long_port[1] = One(G) then
                    equality_check := true;
                else
                    Print("false", "1\n");
                    tf := false;
                fi;
            fi;

            return tf;
        fi;

        if Length(short_port) = 1 then
            # comparing sections
            for i in [2..Length(long_port)] do
                # equality_check := (Section() = long_port[1]);
                
                if Length(long_port[i]) > 1 then
                    # take first (level - 1) elements of the list
                    section_nums := List([1..(level-1)], i -> section_nums[i]);

                    Append(section_nums, [i-1]);

                    # now compare sections
                    for i in [1..Length(section_nums)] do 
                        if i = 1 then
                            current_section := Section(short_port[1], i);
                        else
                            current_section := Section(current_section, i);
                        fi;
                    od;

                    # comparing permutations
                    equality_check := (AutomPortrait(current_section)[1] = long_port[1]);

                    if equality_check = false then
                        tf := false;
                        return false;
                    fi;

                    comparing_portraits_recursive(AutomPortrait(current_section), long_port[i], level + 1, tf, section_nums);

                else
                    # comparing permutations
                    if Length(long_port) = 1 then
                        equality_check := (PermOnLevel(short_port[1], 1) = PermOnLevel(long_port[1],1));
                    else
                        equality_check := (PermOnLevel(short_port[1], 1) = long_port[1]);
                    fi;


                    if equality_check = false then
                        tf := false;
                        return false;
                    fi;
                    comparing_portraits_recursive(AutomPortrait(Section(short_port[1], i-1)), long_port[i], level + 1, tf, section_nums); 
                fi;

                
                if equality_check = false then
                    tf := false;
                    return false;
                fi;
            od;

        else
            # comparing permutations
            if Length(long_port) = 1 then
                equality_check := (short_port[1] = PermOnLevel(long_port[1], 1));
            else
                equality_check := (short_port[1] = long_port[1]);
            fi;

            if equality_check = false then
                    tf := false;
                    return false;
            fi;

            # comparing sections
            for i in [2..Length(long_port)] do
                if Length(long_port[i]) > 1 then
                    # take first (level - 1) elements of the list
                    section_nums := List([1..(level-1)], i -> section_nums[i]);

                    Append(section_nums, [i-1]);
                    comparing_portraits_recursive(short_port[i], long_port[i], level + 1, tf, section_nums);

                else
                    # take first (level - 1) elements of the list
                    section_nums := List([1..(level-1)], i -> section_nums[i]);

                    Append(section_nums, [i-1]);
                    comparing_portraits_recursive(short_port[i], long_port[i], level + 1, tf, section_nums);
                fi;
            od;
        fi;

        return tf;
    end;

    return comparing_portraits_recursive(short_port, long_port, level, answer, sections);
end;

test := comparing_portraits(p2,p1);
