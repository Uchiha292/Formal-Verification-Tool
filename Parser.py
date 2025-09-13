# Parser.py
"""
Parser for the custom mini-language.
This module handles parsing programs written in our custom mini-language.
"""
import re

class Parser:
    def __init__(self):
        self.tokens = []
        self.pos = 0
        self.variables = set()
        self.arrays = {}
        self.array_size = {}

    def tokenize(self, code):
        """Convert code string into tokens."""
        # Remove comments
        code = re.sub(r'//.*', '', code)

        # Define token patterns
        token_patterns = [
            ('NUMBER', r'\d+'),
            ('IDENTIFIER', r'[a-zA-Z][a-zA-Z0-9_]*'),
            ('ASSIGN', r':='),
            ('EQ', r'=='),
            ('NEQ', r'!='),
            ('LTE', r'<='),
            ('GTE', r'>='),
            ('LT', r'<'),
            ('GT', r'>'),
            ('PLUS', r'\+'),
            ('MINUS', r'-'),
            ('MULT', r'\*'),
            ('DIV', r'/'),
            ('LPAREN', r'\('),
            ('RPAREN', r'\)'),
            ('LBRACE', r'\{'),
            ('RBRACE', r'\}'),
            ('LBRACKET', r'\['),
            ('RBRACKET', r'\]'),
            ('SEMICOLON', r';'),
            ('COMMA', r','),
            ('WHITESPACE', r'\s+'),
            ('UNKNOWN', r'.'),
        ]

        token_regex = '|'.join('(?P<%s>%s)' % pair for pair in token_patterns)
        self.tokens = []

        for mo in re.finditer(token_regex, code):
            kind = mo.lastgroup
            value = mo.group()
            if kind == 'WHITESPACE':
                continue
            self.tokens.append((kind, value))

        self.pos = 0
        return self.tokens

    def peek(self):
        """Look at the current token without consuming it."""
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def consume(self):
        """Consume the current token and advance to the next."""
        token = self.peek()
        self.pos += 1
        return token

    def match(self, expected_type):
        """Match and consume a token of the expected type."""
        token = self.peek()
        if token and token[0] == expected_type:
            return self.consume()
        return None

    def expect(self, expected_type):
        """Expect a token of a certain type, raise error if not found."""
        token = self.match(expected_type)
        if token:
            return token
        else:
            current = self.peek()
            raise SyntaxError(f"Expected {expected_type}, got {current[0] if current else 'EOF'}")

    def parse_program(self, code):
        """Parse a complete program."""
        self.tokenize(code)
        statements = []

        while self.pos < len(self.tokens):
            stmt = self.parse_statement()
            if stmt:
                statements.append(stmt)

        return statements

    def parse_statement(self):
        """Parse a statement."""
        token = self.peek()
        if not token:
            return None

        if token[0] == 'IDENTIFIER' and self.tokens[self.pos + 1][0] == 'ASSIGN':
            return self.parse_assignment()
        elif token[0] == 'IDENTIFIER' and token[1] == 'if':
            return self.parse_if_statement()
        elif token[0] == 'IDENTIFIER' and token[1] == 'while':
            return self.parse_while_loop()
        elif token[0] == 'IDENTIFIER' and token[1] == 'for':
            return self.parse_for_loop()
        elif token[0] == 'IDENTIFIER' and token[1] == 'assert':
            return self.parse_assert()
        else:
            # Skip unknown statements
            self.consume()
            if self.match('SEMICOLON'):
                pass
            return {'type': 'skip'}

    def parse_assignment(self):
        """Parse an assignment statement."""
        var_token = self.expect('IDENTIFIER')
        var_name = var_token[1]
        self.variables.add(var_name)

        # Check if this is an array assignment
        if self.match('LBRACKET'):
            index_expr = self.parse_expression()
            self.expect('RBRACKET')
            self.expect('ASSIGN')
            value_expr = self.parse_expression()
            self.expect('SEMICOLON')
            return {
                'type': 'array_assign',
                'array': var_name,
                'index': index_expr,
                'value': value_expr
            }
        else:
            self.expect('ASSIGN')
            expr = self.parse_expression()
            self.expect('SEMICOLON')
            return {
                'type': 'assign',
                'var': var_name,
                'expr': expr
            }

    def parse_if_statement(self):
        """Parse an if statement."""
        self.expect('IDENTIFIER')  # Consume 'if'
        self.expect('LPAREN')
        condition = self.parse_expression()
        self.expect('RPAREN')

        self.expect('LBRACE')
        then_block = []
        while self.peek() and self.peek()[0] != 'RBRACE':
            stmt = self.parse_statement()
            if stmt:
                then_block.append(stmt)
        self.expect('RBRACE')

        else_block = []
        if self.peek() and self.peek()[0] == 'IDENTIFIER' and self.peek()[1] == 'else':
            self.consume()  # Consume 'else'
            self.expect('LBRACE')
            while self.peek() and self.peek()[0] != 'RBRACE':
                stmt = self.parse_statement()
                if stmt:
                    else_block.append(stmt)
            self.expect('RBRACE')

        return {
            'type': 'if',
            'condition': condition,
            'then_block': then_block,
            'else_block': else_block
        }

    def parse_while_loop(self):
        """Parse a while loop."""
        self.expect('IDENTIFIER')  # Consume 'while'
        self.expect('LPAREN')
        condition = self.parse_expression()
        self.expect('RPAREN')

        self.expect('LBRACE')
        body = []
        while self.peek() and self.peek()[0] != 'RBRACE':
            stmt = self.parse_statement()
            if stmt:
                body.append(stmt)
        self.expect('RBRACE')

        return {
            'type': 'while',
            'condition': condition,
            'body': body
        }

    def parse_for_loop(self):
        """Parse a for loop."""
        self.expect('IDENTIFIER')  # Consume 'for'
        self.expect('LPAREN')

        # Initialize
        init = self.parse_statement()

        # Condition
        condition = self.parse_expression()
        self.expect('SEMICOLON')

        # Update
        update = self.parse_statement()

        self.expect('RPAREN')

        # Body
        self.expect('LBRACE')
        body = []
        while self.peek() and self.peek()[0] != 'RBRACE':
            stmt = self.parse_statement()
            if stmt:
                body.append(stmt)
        self.expect('RBRACE')

        return {
            'type': 'for',
            'init': init,
            'condition': condition,
            'update': update,
            'body': body
        }

    def parse_assert(self):
        """Parse an assert statement."""
        self.expect('IDENTIFIER')  # Consume 'assert'
        self.expect('LPAREN')
        condition = self.parse_expression()
        self.expect('RPAREN')
        self.expect('SEMICOLON')

        return {
            'type': 'assert',
            'condition': condition
        }

    def parse_expression(self):
        """Parse an expression."""
        return self.parse_comparison()

    def parse_comparison(self):
        """Parse a comparison expression."""
        left = self.parse_additive()

        if self.peek() and self.peek()[0] in ['EQ', 'NEQ', 'LT', 'GT', 'LTE', 'GTE']:
            op = self.consume()
            right = self.parse_additive()
            return {
                'type': 'binary',
                'op': op[1],
                'left': left,
                'right': right
            }

        return left

    def parse_additive(self):
        """Parse an additive expression."""
        left = self.parse_multiplicative()

        while self.peek() and self.peek()[0] in ['PLUS', 'MINUS']:
            op = self.consume()
            right = self.parse_multiplicative()
            left = {
                'type': 'binary',
                'op': op[1],
                'left': left,
                'right': right
            }

        return left

    def parse_multiplicative(self):
        """Parse a multiplicative expression."""
        left = self.parse_primary()

        while self.peek() and self.peek()[0] in ['MULT', 'DIV']:
            op = self.consume()
            right = self.parse_primary()
            left = {
                'type': 'binary',
                'op': op[1],
                'left': left,
                'right': right
            }

        return left

    def parse_primary(self):
        """Parse a primary expression."""
        token = self.peek()

        if token is None:
            raise SyntaxError("Unexpected end of input")

        if self.match('NUMBER'):
            return {
                'type': 'number',
                'value': int(token[1])
            }
        elif self.match('IDENTIFIER'):
            var_name = token[1]
            self.variables.add(var_name)

            # Check if this is an array access
            if self.peek() and self.peek()[0] == 'LBRACKET':
                self.consume()  # Consume '['
                index = self.parse_expression()
                self.expect('RBRACKET')
                return {
                    'type': 'array_access',
                    'array': var_name,
                    'index': index
                }
            else:
                return {
                    'type': 'variable',
                    'name': var_name
                }
        elif self.match('LPAREN'):
            expr = self.parse_expression()
            self.expect('RPAREN')
            return expr
        else:
            raise SyntaxError(f"Unexpected token: {token}")

def pretty_print_ast(ast, indent=0):
    """Pretty print the AST for debugging."""
    for stmt in ast:
        print('  ' * indent + f"- {stmt['type']}")
        if stmt['type'] == 'assign':
            print('  ' * (indent + 1) + f"var: {stmt['var']}")
            pretty_print_ast([stmt['expr']], indent + 1)
        elif stmt['type'] == 'array_assign':
            print('  ' * (indent + 1) + f"array: {stmt['array']}")
            print('  ' * (indent + 1) + "index:")
            pretty_print_ast([stmt['index']], indent + 2)
            print('  ' * (indent + 1) + "value:")
            pretty_print_ast([stmt['value']], indent + 2)
        elif stmt['type'] in ['if', 'while', 'for']:
            print('  ' * (indent + 1) + "condition:")
            pretty_print_ast([stmt['condition']], indent + 2)
            if stmt['type'] == 'if':
                print('  ' * (indent + 1) + "then:")
                pretty_print_ast(stmt['then_block'], indent + 2)
                print('  ' * (indent + 1) + "else:")
                pretty_print_ast(stmt['else_block'], indent + 2)
            elif stmt['type'] == 'while':
                print('  ' * (indent + 1) + "body:")
                pretty_print_ast(stmt['body'], indent + 2)
            elif stmt['type'] == 'for':
                print('  ' * (indent + 1) + "init:")
                pretty_print_ast([stmt['init']], indent + 2)
                print('  ' * (indent + 1) + "update:")
                pretty_print_ast([stmt['update']], indent + 2)
                print('  ' * (indent + 1) + "body:")
                pretty_print_ast(stmt['body'], indent + 2)
        elif stmt['type'] == 'assert':
            print('  ' * (indent + 1) + "condition:")
            pretty_print_ast([stmt['condition']], indent + 2)
        elif stmt['type'] == 'binary':
            print('  ' * (indent + 1) + f"op: {stmt['op']}")
            print('  ' * (indent + 1) + "left:")
            pretty_print_ast([stmt['left']], indent + 2)
            print('  ' * (indent + 1) + "right:")
            pretty_print_ast([stmt['right']], indent + 2)
        elif stmt['type'] == 'variable':
            print('  ' * (indent + 1) + f"name: {stmt['name']}")
        elif stmt['type'] == 'number':
            print('  ' * (indent + 1) + f"value: {stmt['value']}")
        elif stmt['type'] == 'array_access':
            print('  ' * (indent + 1) + f"array: {stmt['array']}")
            print('  ' * (indent + 1) + "index:")
            pretty_print_ast([stmt['index']], indent + 2)
        elif stmt['type'] == 'skip':
            continue

def pretty_print_expr(expr, indent=0):
    """Pretty print an expression."""
    if expr['type'] == 'number':
        print('  ' * indent + f"number: {expr['value']}")
    elif expr['type'] == 'variable':
        print('  ' * indent + f"variable: {expr['name']}")
    elif expr['type'] == 'array_access':
        print('  ' * indent + f"array_access: {expr['array']}")
        print('  ' * (indent+1) + "index:")
        pretty_print_expr(expr['index'], indent+2)
    elif expr['type'] == 'binary':
        print('  ' * indent + f"binary: {expr['op']}")
        print('  ' * (indent+1) + "left:")
        pretty_print_expr(expr['left'], indent+2)
        print('  ' * (indent+1) + "right:")
        pretty_print_expr(expr['right'], indent+2)
    elif expr['type'] == 'not':
        print('  ' * indent + "not:")
        pretty_print_expr(expr['expr'], indent+1)

# if __name__ == "__main__":
#     # Test the parser with a simple example
#     code = """
#     x = 5;
#     y = x + 3;
#     if (y > 5) {
#        z = y - 1;
#     }

#     """

#     print("Starting parsing...")
#     parser = Parser()
#     ast = parser.parse_program(code)
#     print("Parsed AST:")
#     pretty_print_ast(ast)