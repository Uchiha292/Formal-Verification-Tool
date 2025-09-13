import tkinter as tk
from tkinter import ttk
from graphviz import Digraph
from PIL import Image, ImageTk
import os
import sys
from io import StringIO

# Import backend modules
try:
    from Parser import Parser
    from ssa_converter import SSAConverter, pretty_print_ssa
    from smt_converter import generate_smt_lib
    from Unroll import LoopUnroller
    from verify import ProgramVerifier
except ImportError as e:
    print(f"Error importing backend modules: {e}")
    sys.exit(1)

class FormalVerificationGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Formal Verification Tool")
        self.root.geometry("1300x900")
        self.root.configure(bg="#f0f0f0")

        self.code_font = ("Courier", 10)
        self.label_font = ("Helvetica", 11, "bold")

        self.setup_gui()

    def setup_gui(self):
        main_canvas = tk.Canvas(self.root, bg="#f0f0f0")
        v_scrollbar = tk.Scrollbar(self.root, orient="vertical", command=main_canvas.yview)
        main_canvas.configure(yscrollcommand=v_scrollbar.set)

        v_scrollbar.pack(side="right", fill="y")
        main_canvas.pack(side="left", fill="both", expand=True)

        self.main_frame = tk.Frame(main_canvas, bg="#f0f0f0")
        main_canvas.create_window((0, 0), window=self.main_frame, anchor="nw")
        self.main_frame.bind("<Configure>", lambda e: main_canvas.configure(scrollregion=main_canvas.bbox("all")))

        top_frame = tk.Frame(self.main_frame, bg="#f0f0f0")
        top_frame.pack(fill="x", pady=5)

        self.mode = tk.StringVar(value="verification")
        tk.Radiobutton(top_frame, text="Verification", variable=self.mode, value="verification",
                       command=self.toggle_mode, bg="#f0f0f0").pack(side="left", padx=10)
        tk.Radiobutton(top_frame, text="Equivalence", variable=self.mode, value="equivalence",
                       command=self.toggle_mode, bg="#f0f0f0").pack(side="left", padx=10)

        tk.Label(top_frame, text="Unroll Depth:", bg="#f0f0f0", font=self.label_font).pack(side="left", padx=(0, 5))
        self.unroll_var = tk.IntVar(value=3)
        tk.Spinbox(top_frame, from_=1, to=10, textvariable=self.unroll_var, width=5, font=self.code_font, relief="sunken", bd=1).pack(side="left", padx=5)

        tk.Button(top_frame, text="Run Verification", command=self.run_verification,
                  bg="#4CAF50", fg="white", font=self.label_font, relief="raised", bd=2, padx=10).pack(side="right", padx=(0, 10))

        input_frame = tk.Frame(self.main_frame, bg="#f0f0f0")
        input_frame.pack(fill="both", expand=True, padx=10, pady=5)

        self.verification_input = tk.Text(input_frame, height=12, font=self.code_font, bg="#ffffff", relief="sunken", bd=1)
        self.verification_input.pack(fill="both", expand=True)

        self.equiv_frame = tk.Frame(input_frame, bg="#f0f0f0")
        self.equiv_input1 = tk.Text(self.equiv_frame, height=12, font=self.code_font, bg="#ffffff", relief="sunken", bd=1)
        self.equiv_input2 = tk.Text(self.equiv_frame, height=12, font=self.code_font, bg="#ffffff", relief="sunken", bd=1)

        output_frame = tk.Frame(self.main_frame, bg="#f0f0f0")
        output_frame.pack(fill="both", expand=True, padx=10, pady=5)

        ssa_label = tk.Label(output_frame, text="SSA Panel", font=self.label_font, bg="#f0f0f0")
        ssa_label.grid(row=0, column=0, sticky="w", pady=(0, 2))
        self.ssa_panel = tk.Text(output_frame, height=10, font=self.code_font, bg="#f9f9f9", relief="sunken", bd=1)
        self.ssa_panel.grid(row=1, column=0, sticky="nsew", padx=(0, 5), pady=5)

        smt_label = tk.Label(output_frame, text="SMT Panel", font=self.label_font, bg="#f0f0f0")
        smt_label.grid(row=0, column=1, sticky="w", pady=(0, 2))
        self.smt_panel = tk.Text(output_frame, height=10, font=self.code_font, bg="#f9f9f9", relief="sunken", bd=1)
        self.smt_panel.grid(row=1, column=1, sticky="nsew", padx=(5, 0), pady=5)

        results_label = tk.Label(output_frame, text="Results", font=self.label_font, bg="#f0f0f0")
        results_label.grid(row=2, column=0, sticky="w", columnspan=2, pady=(10, 2))
        self.results_panel = tk.Text(output_frame, height=6, font=self.code_font, bg="#e6f2e6", relief="sunken", bd=1)
        self.results_panel.grid(row=3, column=0, columnspan=2, sticky="nsew", padx=0, pady=5)

        output_frame.grid_columnconfigure(0, weight=1)
        output_frame.grid_columnconfigure(1, weight=1)
        output_frame.grid_rowconfigure(1, weight=1)
        output_frame.grid_rowconfigure(3, weight=0)

        cfg_label = tk.Label(self.main_frame, text="Control Flow Graph (CFG)", font=self.label_font, bg="#f0f0f0")
        cfg_label.pack(pady=(10, 2))
        self.cfg_canvas = tk.Canvas(self.main_frame, width=500, height=350, bg="white", bd=1, relief="sunken")
        self.cfg_canvas.pack(pady=(0, 10))

        bottom_controls_frame = tk.Frame(self.main_frame, bg="#f0f0f0")
        bottom_controls_frame.pack(fill="x", pady=10, padx=10)

        tk.Button(bottom_controls_frame, text="Clear All", command=self.clear_all,
                  bg="#f44336", fg="white", font=self.label_font, relief="raised", bd=2, padx=10).pack(side="left")

        self.root.bind("<MouseWheel>", lambda e: main_canvas.yview_scroll(int(-1 * (e.delta / 120)), "units"))
        self.root.bind("<Button-4>", lambda e: main_canvas.yview_scroll(-1, "units"))
        self.root.bind("<Button-5>", lambda e: main_canvas.yview_scroll(1, "units"))

        self.toggle_mode()

    def toggle_mode(self):
        if self.mode.get() == "verification":
            self.verification_input.pack(fill="both", expand=True)
            self.equiv_frame.pack_forget()
        else:
            self.verification_input.pack_forget()
            self.equiv_frame.pack(fill="both", expand=True)
            self.equiv_input1.pack(side="left", fill="both", expand=True, padx=(0, 5))
            self.equiv_input2.pack(side="left", fill="both", expand=True, padx=(5, 0))

    def run_verification(self):
        self.ssa_panel.delete("1.0", tk.END)
        self.smt_panel.delete("1.0", tk.END)
        self.results_panel.delete("1.0", tk.END)
        self.cfg_canvas.delete("all")

        verifier = ProgramVerifier()
        unroll_depth = self.unroll_var.get()
        verifier.set_unroll_depth(unroll_depth)

        if self.mode.get() == "verification":
            code = self.verification_input.get("1.0", tk.END).strip()
            if not code:
                self.results_panel.insert(tk.END, "Error: No input provided.\n")
                return

            try:
                self.results_panel.insert(tk.END, "Parsing program...\n")
                parser = Parser()
                ast = parser.parse_program(code)
                self.results_panel.insert(tk.END, "Parsing successful.\n")

                self.results_panel.insert(tk.END, "Unrolling loops...\n")
                unroller = LoopUnroller(parser)
                unroller.set_unroll_depth(unroll_depth)
                unrolled_ast = unroller.unroll_program(ast)
                self.results_panel.insert(tk.END, "Unrolling successful.\n")

                self.results_panel.insert(tk.END, "Converting to SSA...\n")
                converter = SSAConverter()
                ssa_program = converter.convert_program(unrolled_ast)
                self.results_panel.insert(tk.END, "SSA conversion successful.\n")
                self.results_panel.insert(tk.END, f"SSA program structure: {str(ssa_program)}\n")

                self.results_panel.insert(tk.END, "Generating SMT-LIB...\n")
                smt_output = generate_smt_lib(ssa_program)
                self.results_panel.insert(tk.END, "SMT-LIB generated.\n")

                self.results_panel.insert(tk.END, "Generating SSA output...\n")
                old_stdout = sys.stdout
                new_stdout = StringIO()
                sys.stdout = new_stdout
                try:
                    pretty_print_ssa(ssa_program)
                    ssa_text = new_stdout.getvalue()
                except Exception as e:
                    self.results_panel.insert(tk.END, f"Error in pretty_print_ssa: {str(e)}\n")
                    ssa_text = ""
                finally:
                    sys.stdout = old_stdout

                if not ssa_text.strip():
                    self.results_panel.insert(tk.END, "Warning: SSA output is empty.\n")
                    ssa_text = self.generate_fallback_ssa(ssa_program)
                    if ssa_text:
                        self.results_panel.insert(tk.END, "Using fallback SSA representation.\n")
                    else:
                        self.results_panel.insert(tk.END, "No fallback SSA available.\n")
                else:
                    self.results_panel.insert(tk.END, "SSA output generated.\n")

                self.ssa_panel.insert(tk.END, f"SSA Form:\n{ssa_text}")
                self.smt_panel.insert(tk.END, smt_output)
                self.results_panel.insert(tk.END, "Outputs displayed.\n")

                self.results_panel.insert(tk.END, "Verifying program...\n")
                has_assertions = any(stmt['type'] == 'ssa_assert' for block in ssa_program for stmt in block.get('statements', []))
                if not has_assertions:
                    self.results_panel.insert(tk.END, "✓ No assertions to verify\n")
                else:
                    result = verifier.verify_program(smt_output)
                    if result['status'] == 'success':
                        self.results_panel.insert(tk.END, "✓ All assertions hold\n")
                    elif result['status'] == 'failed':
                        self.results_panel.insert(tk.END, "✗ Assertion failed\nCounterexample:\n")
                        for var, value in result.get('counterexample', {}).items():
                            self.results_panel.insert(tk.END, f"  {var} = {value}\n")
                    elif result['status'] == 'error':
                        self.results_panel.insert(tk.END, f"Error: {result['message']}\n")
                    else:
                        self.results_panel.insert(tk.END, f"Verification inconclusive: {result['message']}\n")

                self.results_panel.insert(tk.END, "Drawing CFG...\n")
                self.draw_cfg(converter.cfg, ssa_program)
                self.results_panel.insert(tk.END, "CFG drawn.\n")

            except Exception as e:
                self.results_panel.insert(tk.END, f"Error during verification: {str(e)}\n")

        elif self.mode.get() == "equivalence":
            code1 = self.equiv_input1.get("1.0", tk.END).strip()
            code2 = self.equiv_input2.get("1.0", tk.END).strip()

            if not code1 or not code2:
                self.results_panel.insert(tk.END, "Error: Both programs must be provided.\n")
                return

            try:
                self.results_panel.insert(tk.END, "Checking equivalence...\n")
                result = verifier.check_equivalence(code1, code2)
                self.results_panel.insert(tk.END, "Equivalence check completed.\n")

                self.results_panel.insert(tk.END, "Parsing program 1...\n")
                parser = Parser()
                ast1 = parser.parse_program(code1)
                self.results_panel.insert(tk.END, "Program 1 parsed.\n")
                self.results_panel.insert(tk.END, "Parsing program 2...\n")
                ast2 = parser.parse_program(code2)
                self.results_panel.insert(tk.END, "Program 2 parsed.\n")

                self.results_panel.insert(tk.END, "Unrolling programs...\n")
                unroller = LoopUnroller(parser)
                unroller.set_unroll_depth(unroll_depth)
                unrolled_ast1 = unroller.unroll_program(ast1)
                unrolled_ast2 = unroller.unroll_program(ast2)
                self.results_panel.insert(tk.END, "Programs unrolled.\n")

                self.results_panel.insert(tk.END, "Converting to SSA...\n")
                converter = SSAConverter()
                ssa_program1 = converter.convert_program(unrolled_ast1)
                ssa_program2 = converter.convert_program(unrolled_ast2)
                self.results_panel.insert(tk.END, "SSA conversion completed.\n")
                self.results_panel.insert(tk.END, f"SSA program 1 structure: {str(ssa_program1)}\n")
                self.results_panel.insert(tk.END, f"SSA program 2 structure: {str(ssa_program2)}\n")

                self.results_panel.insert(tk.END, "Generating SSA output...\n")
                ssa_output = []
                old_stdout = sys.stdout
                sys.stdout = StringIO()
                try:
                    pretty_print_ssa(ssa_program1)
                    ssa_output.append(sys.stdout.getvalue())
                    sys.stdout = StringIO()
                    pretty_print_ssa(ssa_program2)
                    ssa_output.append("\nProgram 2 SSA:\n")
                    ssa_output.append(sys.stdout.getvalue())
                except Exception as e:
                    self.results_panel.insert(tk.END, f"Error in pretty_print_ssa: {str(e)}\n")
                    ssa_output = []
                finally:
                    sys.stdout = old_stdout

                ssa_text = "".join(ssa_output)
                if not ssa_text.strip():
                    self.results_panel.insert(tk.END, "Warning: SSA output is empty.\n")
                    fallback_ssa1 = self.generate_fallback_ssa(ssa_program1)
                    fallback_ssa2 = self.generate_fallback_ssa(ssa_program2)
                    ssa_text = (fallback_ssa1 or "") + "\nProgram 2 SSA:\n" + (fallback_ssa2 or "")
                    if fallback_ssa1 or fallback_ssa2:
                        self.results_panel.insert(tk.END, "Using fallback SSA representation.\n")
                    else:
                        self.results_panel.insert(tk.END, "No fallback SSA available.\n")
                else:
                    self.results_panel.insert(tk.END, "SSA output generated.\n")

                self.ssa_panel.insert(tk.END, f"SSA Forms:\n{ssa_text}")
                self.smt_panel.insert(tk.END, f"Program 1 SMT:\n{generate_smt_lib(ssa_program1)}\n\nProgram 2 SMT:\n{generate_smt_lib(ssa_program2)}")
                self.results_panel.insert(tk.END, "Outputs displayed.\n")

                if result['equivalent']:
                    self.results_panel.insert(tk.END, "✓ Programs are semantically equivalent\n")
                else:
                    self.results_panel.insert(tk.END, "✗ Programs are NOT equivalent\nCounterexample:\n")
                    for var, value in result.get('counterexample', {}).items():
                        self.results_panel.insert(tk.END, f"  {var} = {value}\n")

                self.results_panel.insert(tk.END, "Drawing CFG...\n")
                self.draw_cfg(converter.cfg, ssa_program1)
                self.results_panel.insert(tk.END, "CFG drawn.\n")

            except Exception as e:
                self.results_panel.insert(tk.END, f"Error during equivalence check: {str(e)}\n")

    def generate_fallback_ssa(self, ssa_program):
        if not ssa_program:
            return ""
        output = []
        for block in ssa_program:
            output.append(f"Block: {block['label']}")
            for stmt in block.get('statements', []):
                if stmt['type'] == 'ssa_assign':
                    output.append(f"  {stmt['var']} := {self.pretty_expr_str(stmt['expr'])}")
                elif stmt['type'] == 'ssa_array_assign':
                    output.append(f"  {stmt['array']} := {stmt['old_array']} with [{self.pretty_expr_str(stmt['index'])}] = {self.pretty_expr_str(stmt['value'])}")
                elif stmt['type'] == 'phi':
                    sources = ", ".join([f"{block}: {var}" for block, var in stmt['sources'].items()])
                    output.append(f"  {stmt['var']} := φ({sources})")
                elif stmt['type'] == 'ssa_if':
                    output.append(f"  if {self.pretty_expr_str(stmt['condition'])}")
                    output.append(f"    then goto {stmt['then_block']}")
                    output.append(f"    else goto {stmt['else_block']}")
                    output.append(f"    join at {stmt['join_block']}")
                elif stmt['type'] == 'ssa_condition':
                    output.append(f"  if {self.pretty_expr_str(stmt['condition'])}")
                    output.append(f"    then goto {stmt['true_target']}")
                    output.append(f"    else goto {stmt['false_target']}")
                elif stmt['type'] == 'ssa_jump':
                    output.append(f"  goto {stmt['target']}")
                elif stmt['type'] == 'ssa_while':
                    output.append(f"  while [{stmt['header_block']}] {self.pretty_expr_str(stmt.get('condition', {'type': 'unknown'}))}")
                    output.append(f"    body {stmt['body_block']}")
                    output.append(f"    exit {stmt['exit_block']}")
                elif stmt['type'] == 'ssa_for':
                    output.append(f"  for")
                    output.append(f"    condition [{stmt['header_block']}]: {self.pretty_expr_str(stmt.get('condition', {'type': 'unknown'}))}")
                    output.append(f"    body: {stmt['body_block']}")
                    output.append(f"    update: {stmt['update_block']}")
                    output.append(f"    exit: {stmt['exit_block']}")
                elif stmt['type'] == 'ssa_assert':
                    output.append(f"  assert {self.pretty_expr_str(stmt['condition'])}")
                else:
                    output.append(f"  Unknown statement type: {stmt['type']}")
            output.append("")
        return "\n".join(output).rstrip()

    def draw_cfg(self, cfg, ssa_program):
        dot = Digraph(format='png')
        for block in ssa_program:
            label = block['label']
            statements = "\n".join([self.pretty_stmt_str(stmt) for stmt in block.get('statements', [])])
            dot.node(label, f"{label}\n{statements}", shape="box")

        for src, dests in cfg.items():
            for dest in dests:
                dot.edge(src, dest)

        try:
            dot.render('cfg', cleanup=True)
            if os.path.exists("cfg.png"):
                cfg_img = Image.open("cfg.png")
                cfg_img = cfg_img.resize((500, 350), Image.Resampling.LANCZOS)
                self.cfg_photo = ImageTk.PhotoImage(cfg_img)
                self.cfg_canvas.create_image(0, 0, anchor='nw', image=self.cfg_photo)
                self.cfg_canvas.image = self.cfg_photo
        except Exception as e:
            self.results_panel.insert(tk.END, f"Error rendering CFG: {str(e)}\n")

    def pretty_stmt_str(self, stmt):
        if stmt['type'] == 'ssa_assign':
            return f"{stmt['var']} := {self.pretty_expr_str(stmt['expr'])}"
        elif stmt['type'] == 'ssa_array_assign':
            return f"{stmt['array']} := {stmt['old_array']} with [{self.pretty_expr_str(stmt['index'])}] = {self.pretty_expr_str(stmt['value'])}"
        elif stmt['type'] == 'phi':
            sources = ", ".join([f"{block}: {var}" for block, var in stmt['sources'].items()])
            return f"{stmt['var']} := φ({sources})"
        elif stmt['type'] == 'ssa_if':
            return f"if {self.pretty_expr_str(stmt['condition'])} then {stmt['then_block']} else {stmt['else_block']}"
        elif stmt['type'] == 'ssa_condition':
            return f"if {self.pretty_expr_str(stmt['condition'])} then {stmt['true_target']} else {stmt['false_target']}"
        elif stmt['type'] == 'ssa_jump':
            return f"goto {stmt['target']}"
        elif stmt['type'] == 'ssa_while':
            return f"while [{stmt['header_block']}]"
        elif stmt['type'] == 'ssa_for':
            return f"for [{stmt['header_block']}]"
        elif stmt['type'] == 'ssa_assert':
            return f"assert {self.pretty_expr_str(stmt['condition'])}"
        return stmt['type']

    def pretty_expr_str(self, expr):
        if not expr:
            return "None"
        if expr['type'] == 'number':
            return str(expr['value'])
        elif expr['type'] == 'variable':
            return expr['name']
        elif expr['type'] == 'array_access':
            return f"{expr['array']}[{self.pretty_expr_str(expr['index'])}]"
        elif expr['type'] == 'binary':
            return f"({self.pretty_expr_str(expr['left'])} {expr['op']} {self.pretty_expr_str(expr['right'])})"
        return f"Unknown expression type: {expr['type']}"

    def clear_all(self):
        self.verification_input.delete("1.0", tk.END)
        self.equiv_input1.delete("1.0", tk.END)
        self.equiv_input2.delete("1.0", tk.END)
        self.ssa_panel.delete("1.0", tk.END)
        self.smt_panel.delete("1.0", tk.END)
        self.results_panel.delete("1.0", tk.END)
        self.cfg_canvas.delete("all")

if __name__ == "__main__":
    window = tk.Tk()
    app = FormalVerificationGUI(window)
    window.mainloop()
