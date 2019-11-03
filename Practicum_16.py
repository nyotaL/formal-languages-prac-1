
from collections import defaultdict
import sys
import unittest
from queue import Queue
from time import sleep

EPS = "EPS"


class State:
    num_instances = 0

    def __init__(self):
        self.num = State.num_instances
        State.num_instances += 1


class OblivionState:
    def __init__(self):
        self.num = -1


class StateMachine:
    # basic constructor for state machine
    # accepting only fixed 1-letter word
    # also can be used as copy-constructor
    def __init__(self, arg):
        if isinstance(arg, str):
            if arg == EPS:
                new_init = State()
                self.states = {new_init}
                self.init = new_init
                self.terminals = {new_init}
                self.triggers = defaultdict(lambda: defaultdict(set))
                self.lastStar = False
                self.regex = "1"
            elif arg in ["a", "b", "c"]:
                new_init = State()
                new_terminal = State()
                self.states = {new_init, new_terminal}
                self.init = new_init
                self.terminals = {new_terminal}
                self.triggers = defaultdict(lambda: defaultdict(set))
                self.triggers[new_init] = {arg: {new_terminal}}
                self.lastStar = False
                self.regex = arg
            else:
                raise ValueError("%s is not permitted symbol" % arg)
        elif isinstance(arg, StateMachine):
            self.states = arg.states
            self.terminals = arg.terminals
            self.init = arg.init
            self.triggers = arg.triggers
            self.lastStar = arg.lastStar
            self.regex = arg.regex

    def add_triggers(self, other):
        for state in other.triggers:
            if state not in self.triggers:
                self.triggers[state] = other.triggers[state]
            else:
                for trigger in self.triggers[state]:
                    self.triggers[state][trigger].update(other.triggers[state][trigger])

    def concatenate(self, other_machine):
        # -------------joining-----------------
        self.states.update(other_machine.states)
        self.add_triggers(other_machine)
        # -----adding new states and triggers--
        for terminal in self.terminals:
            if EPS not in self.triggers[terminal]:
                self.triggers[terminal][EPS] = set()
            self.triggers[terminal][EPS].add(other_machine.init)
        # -----updating init and terminals------
        self.terminals = other_machine.terminals
        self.lastStar = False
        self.regex = "%s%s" % (self.regex, other_machine.regex)
        return self.delete_epsilons()

    def alternate(self, other_machine):
        # -------------joining-----------------
        self.states.update(other_machine.states)
        self.add_triggers(other_machine)
        # -----adding new states and triggers--
        new_init = State()
        self.states.add(new_init)
        self.triggers[new_init] = {EPS: {self.init, other_machine.init}}
        # -----updating init and terminals-----
        self.init = new_init
        self.terminals = self.terminals.union(other_machine.terminals)
        self.lastStar = False
        self.regex = "(%s+%s)" % (self.regex, other_machine.regex)
        return self.delete_epsilons()

    def star(self):
        # multiple consecutive iteration of Kleene star is useless
        if self.lastStar:
            return self

        # -----adding new states and triggers--
        new_init = State()
        self.states.add(new_init)
        self.triggers[new_init] = {EPS: {self.init}}
        for terminal in self.terminals:
            if EPS not in self.triggers[terminal]:
                self.triggers[terminal][EPS] = set()
            self.triggers[terminal][EPS].add(new_init)
        # -----updating init and terminals-----
        self.init = new_init
        self.terminals = {new_init}
        self.lastStar = True
        self.regex = "(%s)*" % self.regex
        return self.delete_epsilons()

    def adjacent(self, state: State, letter):
        try:
            assert state in self.states
        except AssertionError:
            print(self)
            print(state)
            sleep(1)
            raise AssertionError

        if letter not in self.triggers[state]:
            return set()
        else:
            return self.triggers[state][letter]

    @staticmethod
    def parse_from_polish_notation_regex(polish_notation_regex):
        operands = []
        for c in polish_notation_regex:
            # concatenation
            if c == ".":
                if len(operands) < 2:
                    raise ValueError("invalid regular expression: concatenation requires 2 arguments")
                else:
                    mach1 = operands.pop()
                    mach2 = operands.pop()
                    operands.append(mach2.concatenate(mach1))
            elif c == "+":
                if len(operands) < 2:
                    raise ValueError("invalid regular expression: alteration requires 2 arguments")
                else:
                    mach1 = operands.pop()
                    mach2 = operands.pop()
                    operands.append(mach2.alternate(mach1))
            elif c == "*":
                if len(operands) < 1:
                    raise ValueError("invalid regular expression: Klini star requires 1 argument")
                else:
                    mach1 = operands.pop()
                    operands.append(mach1.star())
            elif c in " \t\n\r":
                continue
            elif c == "1":
                operands.append(StateMachine(EPS))
            else:  # c - letter
                operands.append(StateMachine(c))

        if len(operands) != 1:
            raise ValueError("invalid regular expression: stack size must be 1 at the end of parsing")

        return operands.pop()

    def delete_epsilons(self):
        for state in self.states:
            used = {st: False for st in self.states}
            self.transitive_close(state, state, used)
        for state in self.states:
            self.triggers[state].pop(EPS, None)

        to_delete = self.get_unreachable(self.init)
        self.states -= to_delete
        self.terminals -= to_delete
        for state in to_delete:
            self.triggers.pop(state, None)
        return self

    def get_states(self):
        return self.states

    def transitive_close(self, start, cur_state, used):
        used[cur_state] = True
        if cur_state in self.terminals:
            self.terminals.add(start)

        # EPS - continue recursion
        for triggered in self.adjacent(cur_state, EPS):
            if not used[triggered]:
                self.transitive_close(start, triggered, used)

        if cur_state != start:
            for trigger in self.triggers[cur_state]:
                if trigger != EPS:
                    for triggered in self.adjacent(cur_state, trigger):
                        if trigger not in self.triggers[start]:
                            self.triggers[start][trigger] = set()
                        self.triggers[start][trigger].add(triggered)
        return self

    def get_unreachable(self, init):
        marked = {state: False for state in self.states}
        self.dfs(init, marked)

        obsolete = set()
        for state in self.states:
            if not marked[state]:
                obsolete.add(state)
        return obsolete

    def dfs(self, init, marked):
        marked[init] = True
        for trigger in self.triggers[init]:
            for triggered in self.triggers[init][trigger]:
                if not marked[triggered]:
                    self.dfs(triggered, marked)


def recursive_traversal(regex_machine: StateMachine, input_string, init_state: State, way=None):
    if way is None:
        way = []
    if input_string == "":
        return 0

    if input_string[0] not in regex_machine.triggers[init_state]:
        return 0
    else:
        max_len = 0
        for triggered in regex_machine.adjacent(init_state, input_string[0]):
            max_len = max(max_len, 1 + recursive_traversal(regex_machine, input_string[1:], triggered, way + [init_state]))
        return max_len


def max_substring(regex_machine: StateMachine, example: str):
    if example == "":
        return 0
    if example is None:
        raise ValueError("None is not valid argument")

    max_len = 0
    for init_state in regex_machine.get_states():
        for i in range(len(example)):
            max_len = max(max_len, recursive_traversal(regex_machine, example[i:], init_state))
    return max_len


class TestMaxSubstring(unittest.TestCase):
    def test_0(self):
        regex = "aab.ba.+.ba.ab.+a.+aab.ba.+.ba.ab.+a.+."
        # infix form: (a(ab+ba)+(ba+ab)a)(a(ab+ba)+(ba+ab)a)
        example = "aaaababababbbaa"
        # best substring: aaAABABAbabbbaa
        machine = StateMachine.parse_from_polish_notation_regex(regex)

        # print(machine)
        # sleep(2)
        self.assertEqual(max_substring(machine, example), 6)

    def test_1(self):
        regex = "aab.*b..*1a+aa.+."
        # infix form: (a(ab)*b)*((1+a)+aa)
        example = "aaabbaaba"
        # maximal substring: aAABBAAba
        machine = StateMachine.parse_from_polish_notation_regex(regex)

        # print(machine)
        # sleep(2)
        self.assertEqual(max_substring(machine, example), 8)

    def test_2(self):
        regex = "ab+c.aba.*.bac.+.+*"
        example = "babc"
        machine = StateMachine.parse_from_polish_notation_regex(regex)
        self.assertEqual(max_substring(machine, example), 3)

    def test_3(self):
        regex = "acb..bab.c.*.ab.ba.+.+*a."
        example = "abbaa"
        machine = StateMachine.parse_from_polish_notation_regex(regex)
        self.assertEqual(max_substring(machine, example), 5)

    def test_4(self):
        regex = "a*"
        example = "aaaabaabba"
        machine = StateMachine.parse_from_polish_notation_regex(regex)
        self.assertEqual(max_substring(machine, example), 4)

    def test_5(self):
        regex = "ba.ab.+***"
        example = "ababbabaa"
        machine = StateMachine.parse_from_polish_notation_regex(regex)
        self.assertEqual(max_substring(machine, example), 9)

    def test_6(self):
        regex = "a1+*"
        example = "aaaaba"
        machine = StateMachine.parse_from_polish_notation_regex(regex)
        self.assertEqual(max_substring(machine, example), 4)

    def test_7(self):
        regex = "a1+*"
        example = "aaaaba"
        machine = StateMachine(StateMachine.parse_from_polish_notation_regex(regex))
        self.assertEqual(max_substring(machine, example), 4)


def main():
    sys.setrecursionlimit(100000)
    data = input().split()
    regex, example = "".join(data[:-1]), data[-1]

    regex_machine = StateMachine.parse_from_polish_notation_regex(regex)
    print(max_substring(regex_machine, example))

if __name__ == '__main__':
    # unittest.main()
    main()
