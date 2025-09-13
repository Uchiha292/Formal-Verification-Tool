# verify.py
"""
Program verification using Z3 SMT solver.
This module handles:
1. Verifying assertions in a program
2. Checking semantic equivalence between two programs
"""
import sys
import subprocess
import tempfile
import os
from Parser import Parser
from ssa_converter import SSAConverter, pretty_print_ssa
from smt_converter import generate_smt_lib
from Unroll import LoopUnroller

# Try to import Z3 at the top level to detect availability early
try:
    import z3
    Z3_AVAILABLE = True
except ImportError:
    Z3_AVAILABLE = False

class ProgramVerifier:
    def __init__(self):
        self.parser = Parser()
        self.unroller = LoopUnroller(self.parser) 
        self.converter = SSAConverter()
        self.unroll_depth = 3  # Default unroll depth
        
    def set_unroll_depth(self, depth):
        """Set the loop unrolling depth"""
        self.unroll_depth = depth
        self.unroller.set_unroll_depth(depth)
        
    def verify_file(self, filename):
        """Verify a program from a file"""
        with open(filename, 'r') as f:
            program_code = f.read()
        return self.verify_program(program_code)
    
    def verify_program(self, smt_lib):
      """Verify assertions in a program"""        
      try:
          z3_result = self._check_with_z3(smt_lib)
          
          if 'error' in z3_result:
              return {'status': 'error', 'message': z3_result['error']}
          
          # Correct interpretation:
          # - If UNSAT: Assertion holds (no counterexample to its negation)
          # - If SAT: Assertion fails (counterexample exists)
          if z3_result['sat'] == 'unsat':
              return {'status': 'success', 'message': 'All assertions hold'}
          elif z3_result['sat'] == 'sat':
              return {
                  'status': 'failed', 
                  'message': 'Assertion failed',
                  'counterexample': z3_result.get('model', {})
              }
          else:
              return {'status': 'unknown', 'message': 'Verification inconclusive'}
              
      except Exception as e:
          return {'status': 'error', 'message': str(e)}
    
    def check_equivalence(self, program1_code, program2_code):
        """Check if two programs are semantically equivalent"""
        # Parse both programs
        ast1 = self.parser.parse_program(program1_code)
        ast2 = self.parser.parse_program(program2_code)
        
        # Identify all variables in both programs
        program1_vars = self._extract_variables(ast1)
        program2_vars = self._extract_variables(ast2)
        all_vars = program1_vars.union(program2_vars)
        
        # Unroll loops in both programs
        self.unroller.set_unroll_depth(self.unroll_depth)
        unrolled_ast1 = self.unroller.unroll_program(ast1)
        unrolled_ast2 = self.unroller.unroll_program(ast2)
        
        # Convert both to SSA form
        ssa_program1 = self.converter.convert_program(unrolled_ast1)
        ssa_program2 = self.converter.convert_program(unrolled_ast2)
        
        # Generate SMT-LIB for checking equivalence
        smt_lib = self._generate_equivalence_smt(ssa_program1, ssa_program2, all_vars)
        
        # Check equivalence with Z3
        result = self._check_with_z3(smt_lib)
        
        if 'error' in result:
            return {'equivalent': False, 
                    'message': f'Error during equivalence check: {result["error"]}'}
            
        if 'sat' not in result:
            return {'equivalent': False, 
                    'message': 'Unknown error during SMT solving'}

        
        
        if result['sat'] == 'unsat':
            return {'equivalent': True, 'message': 'Programs are semantically equivalent'}
        else:
            return {'equivalent': False, 
                    'message': 'Programs are not equivalent', 
                    'counterexample': result.get('model', {})}
    
    def _extract_variables(self, ast):
        """Extract all variables used in a program"""
        variables = set()
        
        def process_node(node):
            if isinstance(node, dict):
                # Handle variable assignments
                if node.get('type') == 'assign':
                    variables.add(node['var'])
                    process_node(node['expr'])
                # Handle variable references in expressions
                elif node.get('type') == 'variable':
                    variables.add(node['name'])
                # Handle array assignments
                elif node.get('type') == 'array_assign':
                    variables.add(node['array'])
                    process_node(node['index'])
                    process_node(node['value'])
                # Handle array accesses
                elif node.get('type') == 'array_access':
                    variables.add(node['array'])
                    process_node(node['index'])
                # Handle binary operations
                elif node.get('type') == 'binary':
                    process_node(node['left'])
                    process_node(node['right'])
                # Handle if statements
                elif node.get('type') == 'if':
                    process_node(node['condition'])
                    for stmt in node['then_block']:
                        process_node(stmt)
                    for stmt in node['else_block']:
                        process_node(stmt)
                # Handle while loops
                elif node.get('type') == 'while':
                    process_node(node['condition'])
                    for stmt in node['body']:
                        process_node(stmt)
                # Handle for loops
                elif node.get('type') == 'for':
                    if node['init']:
                        process_node(node['init'])
                    process_node(node['condition'])
                    if node['update']:
                        process_node(node['update'])
                    for stmt in node['body']:
                        process_node(stmt)
                # Handle assert statements
                elif node.get('type') == 'assert':
                    process_node(node['condition'])
        
        # Process each statement in the AST
        for stmt in ast:
            process_node(stmt)
            
        return variables
    
    def _generate_equivalence_smt(self, ssa_program1, ssa_program2, variables):
        """Generate SMT-LIB code for checking program equivalence"""
        # Get SMT-LIB for each program
        smt1 = generate_smt_lib(ssa_program1)
        smt2 = generate_smt_lib(ssa_program2)
        
        # Extract the variable declarations and constraints
        smt1_lines = smt1.strip().split('\n')
        smt2_lines = smt2.strip().split('\n')
        
        # Get declarations from program 1
        declarations1 = [line for line in smt1_lines if line.startswith('(declare-const')]
        constraints1 = [line for line in smt1_lines if line.startswith('(assert')]
        
        # Get declarations from program 2, renaming variables to avoid conflicts
        declarations2 = []
        constraints2 = []
        var_mapping = {}
        
        for line in smt2_lines:
            if line.startswith('(declare-const'):
                # Extract variable name
                var = line.split()[1]
                # Create a renamed version
                renamed_var = f"{var}_p2"
                var_mapping[var] = renamed_var
                # Add the renamed declaration
                declarations2.append(f"(declare-const {renamed_var} Int)")
            elif line.startswith('(assert'):
                constraints2.append(line)
        
        # Rename variables in program 2 constraints
        for i, constraint in enumerate(constraints2):
            for var, renamed in var_mapping.items():
                # Replace variable names, being careful with word boundaries
                constraint = constraint.replace(f" {var} ", f" {renamed} ")
                constraint = constraint.replace(f" {var})", f" {renamed})")
                constraint = constraint.replace(f"({var} ", f"({renamed} ")
                constraint = constraint.replace(f"({var})", f"({renamed})")
            constraints2[i] = constraint
        
        # Generate assertions for equality of output variables
        equality_assertions = []
        output_vars = self._identify_output_vars(ssa_program1, ssa_program2)
        
        for var in output_vars:
            # Find the SSA version of each output variable in program 1
            p1_versions = [decl.split()[1] for decl in declarations1 
                          if decl.split()[1].startswith(f"{var}_")]
            if p1_versions:
                p1_final = max(p1_versions, key=lambda x: int(x.split('_')[-1]))
                
                # Find the SSA version of the same variable in program 2
                p2_versions = [var_mapping.get(decl.split()[1], "") for decl in declarations2 
                              if decl.split()[1].startswith(f"{var}_")]
                filtered_versions = [v for v in p2_versions if v]
                if filtered_versions:
                    p2_final = max(filtered_versions, key=lambda x: int(x.split('_')[-1]))                    
                    # Assert that the final values are equal
                    equality_assertions.append(f"(assert (= {p1_final} {p2_final}))")
        
        # Construct the final SMT-LIB for equivalence checking
        combined_smt = [
            "(set-logic QF_AUFLIA)",
            "",
            # Variable declarations
            *declarations1,
            *declarations2,
            "",
            # Constraints from both programs
            *constraints1,
            *constraints2,
            "",
            # Assert the negation of equivalence (to check for satisfiability)
            # If at least one output variable differs, they're not equivalent
            f"(assert (not (and {' '.join(equality_assertions)})))",
            "",
            "(check-sat)",
            "(get-model)"
        ]
        
        return "\n".join(combined_smt)
    
    def _identify_output_vars(self, ssa_program1, ssa_program2):
        """Identify output variables (those that are assigned values)"""
        # For simplicity, treat all variables as potential outputs
        output_vars = set()
        
        # Extract base variable names from SSA variables
        def extract_vars_from_block(block):
            vars_in_block = set()
            for stmt in block["statements"]:
                if stmt["type"] == "ssa_assign":
                    # Extract base variable name (without SSA index)
                    base_var = stmt["var"].split('_')[0]
                    vars_in_block.add(base_var)
                elif stmt["type"] == "ssa_array_assign":
                    base_var = stmt["array"].split('_')[0]
                    vars_in_block.add(base_var)
            return vars_in_block
        
        # Process each block in both programs
        for block in ssa_program1:
            output_vars.update(extract_vars_from_block(block))
            
        for block in ssa_program2:
            output_vars.update(extract_vars_from_block(block))
            
        return output_vars
    
    def _check_with_z3(self, smt_lib):
        """Run Z3 using the Python API with proper error handling"""
        temp_filename = None
        
        # Use Python Z3 API if available
        if Z3_AVAILABLE:
            try:
                solver = z3.Solver()
                solver.from_string(smt_lib)
                result = solver.check()
                
                if result == z3.unsat:
                    return {'sat': 'unsat'}
                elif result == z3.sat:
                    model = solver.model()
                    # Convert model to a readable dictionary
                    model_dict = {}
                    for decl in model.decls():
                        try:
                            # Try to get integer value first
                            model_dict[decl.name()] = model[decl].as_long()
                        except:
                            # Fall back to string representation
                            model_dict[decl.name()] = str(model[decl])
                    return {
                        'sat': 'sat',
                        'model': model_dict
                    }
                else:
                    return {'sat': 'unknown'}
            except Exception as e:
                return {'error': f'Z3 Python API error: {str(e)}'}
        
        # Fall back to command-line Z3 if Python API not available
        try:
            with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as temp:
                temp.write(smt_lib)
                temp_filename = temp.name
            
            # Check if Z3 command exists - look for z3 on Unix/Linux and z3.exe on Windows
            z3_cmd = 'z3.exe' if os.name == 'nt' else 'z3'
            result = subprocess.run([z3_cmd, temp_filename], 
                                capture_output=True, 
                                text=True)
            
            # Check if Z3 command line exists
            if result.returncode == 127 or (os.name == 'nt' and result.returncode == 1):  # Command not found
                return {'error': f'{z3_cmd} executable not found in path. Please ensure it is properly installed and in your PATH.'}
                
            output = result.stdout.strip()
            
            if output.startswith('sat'):
                model_lines = output.split('\n')[1:]
                return {
                    'sat': 'sat',
                    'model': self._parse_z3_model(model_lines)
                }
            elif output.startswith('unsat'):
                return {'sat': 'unsat'}
            else:
                return {'sat': 'unknown', 'output': output}
                
        except FileNotFoundError:
            return {'error': 'Neither z3-solver Python package nor z3 executable found.\n'
                        'Please ensure z3 or z3.exe is in your PATH, or install:\n'
                        '  pip install z3-solver (for Python API)'}
        except Exception as e:
            return {'error': f'Z3 command-line error: {str(e)}'}
        finally:
            if temp_filename and os.path.exists(temp_filename):
                os.remove(temp_filename)
    
    def _parse_z3_model(self, model_lines):
        """Parse Z3's model output into a Python dictionary"""
        model = {}
        current_var = None
        
        for line in model_lines:
            line = line.strip()
            if not line:
                continue
                
            # Check if this is a variable definition
            if line.startswith('(define-fun'):
                # Extract variable name
                current_var = line.split()[1]
                # If it's an SSA variable, get the base name
                if '_' in current_var:
                    base_var = current_var.split('_')[0]
                else:
                    base_var = current_var
                
                # Extract value if it's on the same line
                if "-> Int" in line and line.endswith(")"):
                    value = line.split()[-2]
                    try:
                        model[base_var] = int(value)
                    except ValueError:
                        model[base_var] = value
                        
            # If the value is on the next line
            elif current_var and line.isdigit() or line.startswith('-'):
                base_var = current_var.split('_')[0] if '_' in current_var else current_var
                try:
                    model[base_var] = int(line)
                except ValueError:
                    model[base_var] = line
                current_var = None
                
        return model


'''def main():
    verifier = ProgramVerifier()
    
    if len(sys.argv) < 2:
        print("Usage:")
        print("  verify.py verify <program.txt> [unroll_depth]")
        print("  verify.py equiv <program1.txt> <program2.txt> [unroll_depth]")
        return

    command = sys.argv[1]
    
    # Set unroll depth if provided
    if command == "verify" and len(sys.argv) > 3:
        verifier.set_unroll_depth(int(sys.argv[3]))
    elif command == "equiv" and len(sys.argv) > 4:
        verifier.set_unroll_depth(int(sys.argv[4]))
        
    if command == "verify":
        if len(sys.argv) < 3:
            print("Error: Missing program file")
            return
            
        program_file = sys.argv[2]
        print(f"Verifying program: {program_file}")
        result = verifier.verify_file(program_file)
        
        if result['status'] == 'error':
            print(f"Error: {result['message']}")
        elif result['status'] == 'success':
            print("Verification successful! All assertions hold.")
        elif result['status'] == 'failed':
            print("Verification failed! Found counterexample:")
            for var, value in result['counterexample'].items():
                print(f"  {var} = {value}")
        else:
            print(f"Verification inconclusive: {result['message']}")
            
    elif command == "equiv":
        if len(sys.argv) < 4:
            print("Error: Missing program files")
            return
            
        program1_file = sys.argv[2]
        program2_file = sys.argv[3]
        print(f"Checking equivalence between: {program1_file} and {program2_file}")
        
        with open(program1_file, 'r') as f:
            program1_code = f.read()
        with open(program2_file, 'r') as f:
            program2_code = f.read()
            
        result = verifier.check_equivalence(program1_code, program2_code)
        
        if result['equivalent']:
            print("Programs are semantically equivalent!")
        else:
            print("Programs are NOT equivalent!")
            if 'counterexample' in result:
                print("Counterexample:")
                for var, value in result['counterexample'].items():
                    print(f"  {var} = {value}")
    else:
        print(f"Unknown command: {command}")
        
if __name__ == "__main__":
    main() '''
