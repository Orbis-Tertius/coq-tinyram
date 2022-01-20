"""Emulation of vnTinyRam, via Ben-Sasson et. al. 2020 https://www.scipr-lab.org/doc/TinyRAM-spec-2.000.pdf"""

class vnTinyRAM:
    def __init__(self, word_size: int, num_registers: int):
        self.word_size = word_size  # W in paper
        self.num_registers = num_registers  # K in paper
        self.incr_amount = 2 * self.word_size // 8  # page 8
        # self.state[0] is the program counter and self.state[-1] is the flag.
        self.state = [0] + [None for _ in range(num_registers)] + [0]

    def execute(self, instructions: list) -> None:
        """Mutates self.state"""
        while instructions:
            instruction = instructions[self.state[0]]
            self.state[0] += 1
            if instruction == "load":
                r = instructions[self.state[0]]
                self.state[0] += 1
                val = instructions[self.state[0]]
                self.state[0] += 1
                self.state[int(r)] = val
                instructions = instructions[self.state[0]:]
                self.state[0] = 0
            if instruction == "bitor":
                r1 = instructions[self.state[0]]
                self.state[0] += 1
                r2 = instructions[self.state[0]]
                self.state[0] += 1
                val1 = self.state[int(r1)]
                val2 = self.state[int(r2)]
                val = "".join(str(int(bool(int(x)) or bool(int(y)))) for x,y in zip(val1, val2))
                self.state[int(r1)] = val
                instructions = instructions[self.state[0]:]
                self.state[0] = 0
            print(self.state)

if __name__=="__main__":
    vtr = vnTinyRAM(16, 16)

    instrs = ["load", "1", "0110", "load", "2", "1001", "bitor", "1", "2"]

    vtr.execute(instrs)

    assert vtr.state[1] == "1111"
