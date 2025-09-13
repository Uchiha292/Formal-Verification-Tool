# ssa_converter.py
"""
SSA Converter for the custom mini-language.
This module converts parsed AST from Parser into SSA form.
"""
from Parser import Parser

class SSAConverter:
    def __init__(self):
        self.var_versions = {}  # Tracks the latest version of each variable
        self.phi_functions = {}
        self.counter = 0
        self.current_block = "entry"
        self.blocks = {"entry": []}
        self.cfg = {}  # Control flow graph

    def fresh_var(self, base_name):
        """Generate a fresh variable name with incremented version number."""
        if base_name not in self.var_versions:
            self.var_versions[base_name] = 0
            return f"{base_name}_0"
        else:
            self.var_versions[base_name] += 1
            return f"{base_name}_{self.var_versions[base_name]}"

    def fresh_label(self, prefix="L"):
        """Generate a unique label for code blocks."""
        self.counter += 1
        return f"{prefix}{self.counter}"

    def convert_program(self, ast):
        """Convert the entire program AST to SSA form."""
        for stmt in ast:
            ssa_stmt = self.convert_statement(stmt)
            if ssa_stmt:
                if isinstance(ssa_stmt, list):
                    self.blocks[self.current_block].extend(ssa_stmt)
                else:
                    self.blocks[self.current_block].append(ssa_stmt)

        # Assemble the final SSA program from all blocks
        ssa_program = []
        for block_name, block_stmts in self.blocks.items():
            ssa_program.append({"type": "block", "label": block_name, "statements": block_stmts})
        return ssa_program

    def convert_statement(self, stmt):
        """Convert a single statement to SSA form."""
        if not stmt:
            return None

        stmt_type = stmt.get('type')
        handlers = {
            'assign': self.convert_assignment,
            'array_assign': self.convert_array_assignment,
            'if': self.convert_if_statement,
            'while': self.convert_while_loop,
            'for': self.convert_for_loop,
            'assert': self.convert_assert,
            'skip': lambda x: None
        }
        return handlers.get(stmt_type, self.handle_unknown)(stmt)

    def handle_unknown(self, stmt):
        """Handle unknown statement types."""
        raise ValueError(f"Unknown statement type: {stmt.get('type')}")

    def convert_assignment(self, stmt):
        """Convert an assignment statement to SSA form."""
        var_name = stmt['var']
        expr_ssa = self.convert_expression(stmt['expr'])

        # Increment version only when creating a new assignment
        self.var_versions[var_name] = self.var_versions.get(var_name, -1) + 1
        new_var = f"{var_name}_{self.var_versions[var_name]}"

        return {"type": "ssa_assign", "var": new_var, "expr": expr_ssa}

    def convert_array_assignment(self, stmt):
        """Convert an array assignment statement to SSA form."""
        array_name = stmt['array']
        index_ssa = self.convert_expression(stmt['index'])
        value_ssa = self.convert_expression(stmt['value'])
        # Get current version before creating a new one
        old_array = self.get_current_version(array_name)
        new_array = self.fresh_var(array_name)
        return {
            "type": "ssa_array_assign",
            "array": new_array,
            "old_array": old_array,
            "index": index_ssa,
            "value": value_ssa
        }

    def convert_if_statement(self, stmt):
        """Convert an if statement to SSA form."""
        condition_ssa = self.convert_expression(stmt['condition'])

        # Save current state before processing branches
        parent_block = self.current_block
        parent_versions = self.var_versions.copy()

        # Create blocks for then, else, and join
        then_label = self.fresh_label("then")
        else_label = self.fresh_label("else")
        join_label = self.fresh_label("join")

        # Create the if statement first in the PARENT block
        ssa_if_stmt = {
            "type": "ssa_if",
            "condition": condition_ssa,
            "then_block": then_label,
            "else_block": else_label,
            "join_block": join_label
        }

        # Add the if statement to the current (parent) block
        self.blocks[parent_block].append(ssa_if_stmt)

        # Update control flow graph
        self.cfg.setdefault(parent_block, []).extend([then_label, else_label])
        self.cfg.setdefault(then_label, []).append(join_label)
        self.cfg.setdefault(else_label, []).append(join_label)

        # Process then block with a separate variable version namespace
        self.current_block = then_label
        self.blocks[then_label] = []

        # Copy parent versions for the then block
        self.var_versions = parent_versions.copy()

        # Now process the block statements
        for s in stmt['then_block']:
            then_stmt = self.convert_statement(s)
            if then_stmt:
                if isinstance(then_stmt, list):
                    self.blocks[then_label].extend(then_stmt)
                else:
                    self.blocks[then_label].append(then_stmt)

        # Save then branch final variable versions
        then_final_versions = self.var_versions.copy()

        # Process else block with a separate variable version namespace
        self.current_block = else_label
        self.blocks[else_label] = []

        # Copy only relevant versions for the else block
        self.var_versions = parent_versions.copy()

        # Now process the block statements
        for s in stmt['else_block']:
            # Ensure we reference the latest version from the then block if used
            if 'var' in s and s['var'] in then_final_versions:
                # Increment the current variable version by 1
                current_version = then_final_versions[s['var']] + 1
                s['var'] = f"{s['var']}_{current_version - 1}"

            else_stmt = self.convert_statement(s)
            if else_stmt:
                if isinstance(else_stmt, list):
                    self.blocks[else_label].extend(else_stmt)
                else:
                   self.blocks[else_label].append(else_stmt)

        # Save else branch final variable versions
        else_final_versions = self.var_versions.copy()

        # Set up join block
        self.current_block = join_label
        self.blocks[join_label] = []

        # Create phi functions for variables modified in either branch
        modified_vars = set()
        all_vars = set(then_final_versions.keys()).union(set(else_final_versions.keys()))

        for var in all_vars:
            parent_ver = parent_versions.get(var, 0)
            then_ver = then_final_versions.get(var, parent_ver)
            else_ver = else_final_versions.get(var, parent_ver)

            # If the variable was modified in either branch
            if then_ver != parent_ver or else_ver != parent_ver:
                modified_vars.add(var)

        # Create phi functions and update variable versions
        phi_statements = []

        # Update the phi function creation in convert_if_statement
        for var in modified_vars:
            # Get the correct version from each branch
            then_ver = then_final_versions.get(var, parent_versions.get(var, 0))
            else_ver = else_final_versions.get(var, parent_versions.get(var, 0))

            then_var = f"{var}_{then_ver}"
            else_var = f"{var}_{else_ver}"

            # Create new versions for the phi function
            self.var_versions[var] = max(then_ver, else_ver) + 1
            new_var = f"{var}_{self.var_versions[var]}"

            phi_statements.append({
               "type": "phi",
                "var": new_var,
                "sources": {then_label: then_var, else_label: else_var}
            })

        # Add phi statements to join block
        self.blocks[join_label].extend(phi_statements)

        # Return None since we've already added the if statement to the parent block
        return None

    def convert_while_loop(self, stmt):
        """Convert a while loop to SSA form."""
        # Create block labels
        header_label = self.fresh_label("while_header")
        body_label = self.fresh_label("while_body")
        exit_label = self.fresh_label("while_exit")

        # Save parent block and variable versions
        parent_block = self.current_block
        parent_versions = self.var_versions.copy()

        # Create the while statement in the parent block
        ssa_while_stmt = {
            "type": "ssa_while",
            "header_block": header_label,
            "body_block": body_label,
            "exit_block": exit_label
        }

        # Add the while statement to the parent block
        self.blocks[parent_block].append(ssa_while_stmt)

        # Update CFG
        self.cfg.setdefault(parent_block, []).append(header_label)

        # Initialize header block with placeholders for phi functions
        self.current_block = header_label
        self.blocks[header_label] = []

        # Copy parent versions for initial header processing
        header_versions = parent_versions.copy()
        self.var_versions = header_versions

        # Convert condition in header block context
        condition_ssa = self.convert_expression(stmt['condition'])

        # Add condition to header block
        self.blocks[header_label].append({
            "type": "ssa_condition",
            "condition": condition_ssa,
            "true_target": body_label,
            "false_target": exit_label
        })

        # Save header block variable versions after condition evaluation
        header_after_condition_versions = self.var_versions.copy()

        # Initialize and process body block
        self.current_block = body_label
        self.blocks[body_label] = []
        body_init_versions = header_after_condition_versions.copy()
        self.var_versions = body_init_versions

        for s in stmt['body']:
            body_stmt = self.convert_statement(s)
            if body_stmt:
                if isinstance(body_stmt, list):
                    self.blocks[body_label].extend(body_stmt)
                else:
                    self.blocks[body_label].append(body_stmt)

        # Add jump back to header at end of body
        self.blocks[body_label].append({
            "type": "ssa_jump",
            "target": header_label
        })

        # Save body block variable versions after processing
        body_final_versions = self.var_versions.copy()

        # Update CFG for the loop structure
        self.cfg.setdefault(header_label, []).extend([body_label, exit_label])
        self.cfg.setdefault(body_label, []).append(header_label)

        # Identify variables modified in loop body
        modified_vars = set()
        for var in body_final_versions:
            if var not in parent_versions or parent_versions[var] != body_final_versions[var]:
                modified_vars.add(var)

        # Create phi functions for the header block
        phi_statements = []

        # Track the new versions that will be created by phi functions
        new_header_versions = parent_versions.copy()

        for var in modified_vars:
            # Get versions from entry and body
            entry_ver = parent_versions.get(var, 0)
            body_ver = body_final_versions.get(var, 0)

            entry_var = f"{var}_{entry_ver}"
            body_var = f"{var}_{body_ver}"

            # Increment version for phi result
            new_header_versions[var] = max(entry_ver, body_ver) + 1
            new_var = f"{var}_{new_header_versions[var]}"

            phi_statements.append({
                "type": "phi",
                "var": new_var,
                "sources": {parent_block: entry_var, body_label: body_var}
            })

        # Insert phi statements at the beginning of header block
        self.blocks[header_label] = phi_statements + self.blocks[header_label]

        # Update variable versions with those from phi functions
        self.var_versions = new_header_versions

        # Set up exit block
        self.current_block = exit_label
        self.blocks[exit_label] = []

        # Update the while statement condition in the parent block
        ssa_while_stmt["condition"] = condition_ssa

        # Return None since we've already added the while statement to the parent block
        return None

    def convert_for_loop(self, stmt):
        """Convert a for loop to SSA form."""
        # Process initialization
        init_statements = []
        if stmt['init']:
            init_ssa = self.convert_statement(stmt['init'])
            if init_ssa:
                init_statements.extend(init_ssa if isinstance(init_ssa, list) else [init_ssa])

        # Create block labels
        header_label = self.fresh_label("for_header")
        body_label = self.fresh_label("for_body")
        update_label = self.fresh_label("for_update")
        exit_label = self.fresh_label("for_exit")

        # Save parent block and variable versions after initialization
        parent_block = self.current_block
        parent_versions = self.var_versions.copy()

        # Create for loop statement in parent block
        ssa_for_stmt = {
            "type": "ssa_for",
            "init_block": parent_block,
            "header_block": header_label,
            "body_block": body_label,
            "update_block": update_label,
            "exit_block": exit_label
        }

        # Add the for statement to the parent block
        self.blocks[parent_block].append(ssa_for_stmt)

        # Update CFG
        self.cfg.setdefault(parent_block, []).append(header_label)

        # Add init statements to parent block
        self.blocks.setdefault(parent_block, []).extend(init_statements)

        # Create header block for condition
        self.current_block = header_label
        self.blocks[header_label] = []
        header_versions = parent_versions.copy()
        self.var_versions = header_versions

        # Convert condition in header block context
        condition_ssa = self.convert_expression(stmt['condition'])

        # Add condition to header block
        self.blocks[header_label].append({
            "type": "ssa_condition",
            "condition": condition_ssa,
            "true_target": body_label,
            "false_target": exit_label
        })

        # Process body block
        self.current_block = body_label
        self.blocks[body_label] = []
        body_versions = self.var_versions.copy()
        self.var_versions = body_versions

        for s in stmt['body']:
            body_stmt = self.convert_statement(s)
            if body_stmt:
                if isinstance(body_stmt, list):
                    self.blocks[body_label].extend(body_stmt)
                else:
                    self.blocks[body_label].append(body_stmt)

        # Add jump to update block at end of body
        self.blocks[body_label].append({
            "type": "ssa_jump",
            "target": update_label
        })

        # Save body block variable versions
        body_final_versions = self.var_versions.copy()

        # Process update block
        self.current_block = update_label
        self.blocks[update_label] = []
        update_versions = body_final_versions.copy()
        self.var_versions = update_versions

        if stmt['update']:
            update_stmt = self.convert_statement(stmt['update'])
            if update_stmt:
                if isinstance(update_stmt, list):
                    self.blocks[update_label].extend(update_stmt)
                else:
                    self.blocks[update_label].append(update_stmt)

        # Add jump back to header at end of update
        self.blocks[update_label].append({
            "type": "ssa_jump",
            "target": header_label
        })

        # Save update block variable versions
        update_final_versions = self.var_versions.copy()

        # Update CFG
        self.cfg.setdefault(header_label, []).extend([body_label, exit_label])
        self.cfg.setdefault(body_label, []).append(update_label)
        self.cfg.setdefault(update_label, []).append(header_label)

        # Identify variables modified in loop body/update
        modified_vars = set()
        for var in update_final_versions:
            if var not in parent_versions or parent_versions[var] != update_final_versions[var]:
                modified_vars.add(var)

        # Create phi functions for header block
        phi_statements = []
        header_phi_vars = {}

        for var in modified_vars:
            parent_var = f"{var}_{parent_versions.get(var, 0)}"
            update_var = f"{var}_{update_final_versions[var]}"

            # Create a new version for the header phi
            new_var = self.fresh_var(var)
            header_phi_vars[var] = int(new_var.split('_')[1])

            phi_statements.append({
                "type": "phi",
                "var": new_var,
                "sources": {parent_block: parent_var, update_label: update_var}
            })

        # Insert phi statements at the beginning of header block
        self.blocks[header_label] = phi_statements + self.blocks[header_label]

        # Set up exit block with the final variable versions
        self.current_block = exit_label
        self.blocks[exit_label] = []

        # Merge variable versions from header for exit block
        for var, version in header_versions.items():
            if var in header_phi_vars:
                self.var_versions[var] = header_phi_vars[var]
            else:
                self.var_versions[var] = version

        # Update the for statement condition in the parent block
        ssa_for_stmt["condition"] = condition_ssa

        # Return None since we've already added the for statement to the parent block
        return None

    def convert_assert(self, stmt):
        """Convert an assert statement to SSA form."""
        return {
            "type": "ssa_assert",
            "condition": self.convert_expression(stmt['condition'])
        }

    def convert_expression(self, expr):
        """Convert an expression to SSA form."""
        if not expr:
            return None

        handlers = {
            'number': lambda e: {'type': 'number', 'value': e['value']},
            'variable': self.handle_variable,
            'array_access': self.handle_array_access,
            'binary': self.handle_binary
        }
        return handlers[expr['type']](expr)

    def handle_variable(self, expr):
        """Handle a variable expression in SSA form."""
        return {'type': 'variable', 'name': self.get_current_version(expr['name'])}

    def handle_array_access(self, expr):
        """Handle an array access expression in SSA form."""
        return {
            'type': 'array_access',
            'array': self.get_current_version(expr['array']),
            'index': self.convert_expression(expr['index'])
        }

    def handle_binary(self, expr):
        """Handle a binary expression in SSA form."""
        return {
            'type': 'binary',
            'op': expr['op'],
            'left': self.convert_expression(expr['left']),
            'right': self.convert_expression(expr['right'])
        }

    def get_current_version(self, var_name):
        """Get the current version of a variable."""
        if var_name not in self.var_versions:
            self.var_versions[var_name] = 0
        return f"{var_name}_{self.var_versions[var_name]}"


def pretty_print_ssa(ssa_program, indent=0):
    """Pretty print the SSA program for debugging."""
    for block in ssa_program:
        print('  ' * indent + f"Block: {block['label']}")
        for stmt in block['statements']:
            pretty_print_ssa_stmt(stmt, indent + 1)

def pretty_print_ssa_stmt(stmt, indent=0):
    """Pretty print a single SSA statement."""
    if stmt['type'] == 'ssa_assign':
        print('  ' * indent + f"{stmt['var']} := {pretty_expr_str(stmt['expr'])}")
    elif stmt['type'] == 'ssa_array_assign':
        print('  ' * indent + f"{stmt['array']} := {stmt['old_array']} with [{pretty_expr_str(stmt['index'])}] = {pretty_expr_str(stmt['value'])}")
    elif stmt['type'] == 'phi':
        sources_str = ", ".join([f"{block}: {var}" for block, var in stmt['sources'].items()])
        print('  ' * indent + f"{stmt['var']} := φ({sources_str})")
    elif stmt['type'] == 'ssa_if':
        print('  ' * indent + f"if {pretty_expr_str(stmt['condition'])}")
        print('  ' * indent + f"  then goto {stmt['then_block']}")
        print('  ' * indent + f"  else goto {stmt['else_block']}")
        print('  ' * indent + f"join at {stmt['join_block']}")
    elif stmt['type'] == 'ssa_condition':
        print('  ' * indent + f"if {pretty_expr_str(stmt['condition'])}")
        print('  ' * indent + f"  then goto {stmt['true_target']}")
        print('  ' * indent + f"  else goto {stmt['false_target']}")
    elif stmt['type'] == 'ssa_jump':
        print('  ' * indent + f"goto {stmt['target']}")
    elif stmt['type'] == 'ssa_while':
        print('  ' * indent + f"while [{stmt['header_block']}] {pretty_expr_str(stmt.get('condition', 'condition in header'))}")
        print('  ' * indent + f"  body {stmt['body_block']}")
        print('  ' * indent + f"  exit {stmt['exit_block']}")
    elif stmt['type'] == 'ssa_for':
        print('  ' * indent + "for")
        print('  ' * (indent + 1) + f"condition [{stmt['header_block']}]: {pretty_expr_str(stmt.get('condition', 'condition in header'))}")
        print('  ' * (indent + 1) + f"body: {stmt['body_block']}")
        print('  ' * (indent + 1) + f"update: {stmt['update_block']}")
        print('  ' * (indent + 1) + f"exit: {stmt['exit_block']}")
    elif stmt['type'] == 'ssa_assert':
        print('  ' * indent + f"assert {pretty_expr_str(stmt['condition'])}")
    else:
        print('  ' * indent + f"Unknown statement type: {stmt['type']}")

def pretty_expr_str(expr):
    """Convert an expression to a string for pretty printing."""
    if not expr:
        return "None"
    if expr['type'] == 'number':
        return str(expr['value'])
    elif expr['type'] == 'variable':
        return expr['name']
    elif expr['type'] == 'array_access':
        return f"{expr['array']}[{pretty_expr_str(expr['index'])}]"
    elif expr['type'] == 'binary':
        return f"({pretty_expr_str(expr['left'])} {expr['op']} {pretty_expr_str(expr['right'])})"
    else:
        return f"Unknown expression type: {expr['type']}"