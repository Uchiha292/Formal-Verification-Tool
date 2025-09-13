# improved unroll
import copy

def pretty_expr_str(expr):
    """Convert an expression to a pretty string."""
    if expr['type'] == 'number':
        return str(expr['value'])
    
    elif expr['type'] == 'variable':
        return expr['name']
    
    elif expr['type'] == 'binary':
        left = pretty_expr_str(expr['left'])
        right = pretty_expr_str(expr['right'])
        return f"({left} {expr['op']} {right})"
    
    elif expr['type'] == 'array_access':
        array = expr['array']
        index = pretty_expr_str(expr['index'])
        return f"{array}[{index}]"
    
    else:
        return f"<{expr['type']}>"

class LoopUnroller:
    def __init__(self, parser):
        self.parser = parser
        self.unroll_depth = 3  # Default unroll depth

    def set_unroll_depth(self, depth):
        self.unroll_depth = depth

    def unroll_program(self, program):
        unrolled = []

        for stmt in program:
        
            if stmt['type'] == 'while':
                unrolled.extend(self.unroll_while_loop(stmt))
        
            elif stmt['type'] == 'for':
                unrolled.extend(self.unroll_for_loop(stmt))
        
            elif stmt['type'] == 'if':
                then_block = self.unroll_program(stmt['then_block'])
                else_block = self.unroll_program(stmt['else_block'])
                unrolled.append({
                    'type': 'if',
                    'condition': stmt['condition'],
                    'then_block': then_block,
                    'else_block': else_block
                })
        
            else:
                unrolled.append(stmt)  # Handle other statement types directly

        return unrolled

    def unroll_while_loop(self, loop):
        result = []
        condition = loop['condition']
        body = loop['body']

        # Create a sequence of if conditions for each iteration
        for i in range(self.unroll_depth):
            # Add if-statement for this iteration
            if_block = {
                'type': 'if',
                'condition': copy.deepcopy(condition),
                'then_block': self.unroll_program(copy.deepcopy(body)),
                'else_block': []  # No else needed for while
            }
            result.append(if_block)
            
            # For the final iteration, add an assertion that the loop condition is false
            # to model the loop termination
            if i == self.unroll_depth - 1:
                # Create a negated condition for the assertion
                negated_condition = self.negate_condition(copy.deepcopy(condition))
                result.append({
                    'type': 'assert',
                    'condition': negated_condition
                })

        return result

    def unroll_for_loop(self, loop):
        result = []
        init = loop['init']
        condition = loop['condition']
        update = loop['update']
        body = loop['body']

        # Add initialization
        if init:
            result.append(init)

        # Create a sequence of if conditions for each iteration
        for i in range(self.unroll_depth):
            # Add if-statement for this iteration
            unrolled_body = self.unroll_program(copy.deepcopy(body))
            
            if_block = {
                'type': 'if',
                'condition': copy.deepcopy(condition),
                'then_block': unrolled_body + [copy.deepcopy(update)] if update else unrolled_body,
                'else_block': []  # No else needed for for
            }
            result.append(if_block)
            
            # For the final iteration, add an assertion that the loop condition is false
            # to model the loop termination
            if i == self.unroll_depth - 1:
                # Create a negated condition for the assertion
                negated_condition = self.negate_condition(copy.deepcopy(condition))
                result.append({
                    'type': 'assert',
                    'condition': negated_condition
                })

        return result

    def negate_condition(self, condition):
        """Negate a condition expression."""
        if condition['type'] == 'binary':
            # Invert comparison operators
            op_map = {
                '==': '!=',
                '!=': '==',
                '<': '>=',
                '>': '<=',
                '<=': '>',
                '>=': '<'
            }
            
            if condition['op'] in op_map:
                # Directly negate by changing the operator
                condition['op'] = op_map[condition['op']]
                return condition
        
        # For more complex conditions, create a new binary expression with a '!=' operator
        return {
            'type': 'binary',
            'op': '==',
            'left': condition,
            'right': {'type': 'number', 'value': 0}
        }

    def pretty_print_unrolled_program(self, program, indent=0):
        """Pretty print the unrolled program."""
        for stmt in program:
            if stmt['type'] == 'assign':
                print(' ' * indent + f"{stmt['var']} := {pretty_expr_str(stmt['expr'])};")
        
            elif stmt['type'] == 'array_assign':
                print(' ' * indent + f"{stmt['array']}[{pretty_expr_str(stmt['index'])}] := {pretty_expr_str(stmt['value'])};")
        
            elif stmt['type'] == 'if':
                print(' ' * indent + f"if ({pretty_expr_str(stmt['condition'])}) {{")
                self.pretty_print_unrolled_program(stmt['then_block'], indent + 4)
                print(' ' * indent + "}")
        
                if stmt['else_block']:
                    print(' ' * indent + "else {")
                    self.pretty_print_unrolled_program(stmt['else_block'], indent + 4)
                    print(' ' * indent + "}")
        
            elif stmt['type'] == 'while':
                print(' ' * indent + f"while ({pretty_expr_str(stmt['condition'])}) {{")
                self.pretty_print_unrolled_program(stmt['body'], indent + 4)
                print(' ' * indent + "}")
        
            elif stmt['type'] == 'for':
                print(' ' * indent + "for (", end="")
        
                if stmt['init']:
                    if stmt['init']['type'] == 'assign':
                        print(f"{stmt['init']['var']} := {pretty_expr_str(stmt['init']['expr'])}", end="")
        
                print("; ", end="")
                print(f"{pretty_expr_str(stmt['condition'])}; ", end="")
        
                if stmt['update'] and stmt['update']['type'] == 'assign':
                    print(f"{stmt['update']['var']} := {pretty_expr_str(stmt['update']['expr'])}", end="")
        
                print(") {")
                self.pretty_print_unrolled_program(stmt['body'], indent + 4)
                print(' ' * indent + "}")
        
            elif stmt['type'] == 'assert':
                print(' ' * indent + f"assert({pretty_expr_str(stmt['condition'])});")
        
            else:
                print(' ' * indent + f"// Unsupported statement type: {stmt['type']}")