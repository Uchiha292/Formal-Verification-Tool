# smt_converter.py
# smt_generator.py
from typing import Dict, List

class SMTGenerator:
    def __init__(self):
        self.declarations = set()
        self.constraints = []
        self.current_assertions = []
        self.join_conditions: Dict[str, Dict] = {}
        self.var_map = {}

    def generate_smt(self, ssa_program) -> List[str]:
        # First pass: Build join block condition map
        self._build_join_condition_map(ssa_program)

        # Second pass: Generate constraints
        for block in ssa_program:
            self._process_block(block)

        return [
            *[f"(declare-const {v} Int)" for v in self.declarations],
            "",
            *self.constraints,
            "",
            *self.current_assertions
        ]

    def _build_join_condition_map(self, ssa_program):
        """Create mapping from join blocks to their controlling conditions"""
        for block in ssa_program:
            for stmt in block["statements"]:
                if stmt["type"] == "ssa_if":
                    self.join_conditions[stmt["join_block"]] = {
                        "condition": stmt["condition"],
                        "then_block": stmt["then_block"],
                        "else_block": stmt["else_block"]
                    }

    def _process_block(self, block):
        for stmt in block["statements"]:
            handler = {
                "ssa_assign": self._handle_assign,
                "ssa_array_assign": self._handle_array_assign,
                "phi": self._handle_phi,
                "ssa_assert": self._handle_assert,
                "ssa_if": self._handle_if
            }.get(stmt["type"], lambda x: None)

            handler(stmt)

    def _declare_var(self, var_name):
        if var_name not in self.declarations:
            self.declarations.add(var_name)
            self.var_map[var_name] = var_name

    def _handle_assign(self, stmt):
        var = stmt["var"]
        expr = self._convert_expr(stmt["expr"])
        self._declare_var(var)
        self.constraints.append(f"(assert (= {var} {expr}))")

    def _handle_array_assign(self, stmt):
        array_var = stmt["array"]
        old_array = stmt["old_array"]
        index = self._convert_expr(stmt["index"])
        value = self._convert_expr(stmt["value"])

        self._declare_var(array_var)
        self.constraints.append(
            f"(assert (= {array_var} (store {old_array} {index} {value})))"
        )

    def _handle_phi(self, stmt):
        join_block = [k for k, v in self.join_conditions.items()
                     if v["then_block"] in stmt["sources"]
                     and v["else_block"] in stmt["sources"]][0]

        condition = self._convert_expr(
            self.join_conditions[join_block]["condition"]
        )

        then_var = stmt["sources"][self.join_conditions[join_block]["then_block"]]
        else_var = stmt["sources"][self.join_conditions[join_block]["else_block"]]
        phi_var = stmt["var"]

        self._declare_var(phi_var)
        self.constraints.append(
            f"(assert (= {phi_var} (ite {condition} {then_var} {else_var})))"
        )

    def _handle_assert(self, stmt):
        expr = self._convert_expr(stmt["condition"])
        self.current_assertions.append(f"(assert (not {expr}))")

    def _handle_if(self, stmt):
        # Handled in join condition map
        pass

    def _convert_expr(self, expr) -> str:
        if expr["type"] == "number":
            return str(expr["value"])
        if expr["type"] == "variable":
            return self.var_map.get(expr["name"], expr["name"])
        if expr["type"] == "array_access":
            array = self._convert_expr(expr["array"])
            index = self._convert_expr(expr["index"])
            return f"(select {array} {index})"
        if expr["type"] == "binary":
            left = self._convert_expr(expr["left"])
            right = self._convert_expr(expr["right"])
            op = {
                "+": "+", "-": "-", "*": "*", "/": "div",
                "==": "=", "!=": "distinct",
                "<": "<", ">": ">", "<=": "<=", ">=": ">="
            }[expr["op"]]
            return f"({op} {left} {right})"
        raise ValueError(f"Unsupported expression type: {expr['type']}")

def generate_smt_lib(ssa_program) -> str:
    generator = SMTGenerator()
    constraints = generator.generate_smt(ssa_program)
    return "\n".join([
        "(set-logic QF_AUFLIA)",
        ""
    ] + constraints + [
        "(check-sat)",
        "(get-model)"
    ])

