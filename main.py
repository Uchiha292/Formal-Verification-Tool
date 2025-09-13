# updated main
import sys
import textwrap
from Parser import Parser
from ssa_converter import SSAConverter, pretty_print_ssa
from smt_converter import generate_smt_lib
from Unroll import LoopUnroller
from verify import ProgramVerifier

def main():

    code = textwrap.dedent("""
      sum := 10;
      for (i := 1; i <= 10; i := i + 1;) {
        sum := sum + i;
        }      
        """)


# Equivalence Check
    program1_code = textwrap.dedent("""
      sum := 10;
      for (i := 1; i <= 10; i := i + 1;) {
        sum := sum + i;
        }
      """)

    program2_code = textwrap.dedent("""
      sum := 0;
        i := 5;
        while (i >= 1) {
            sum := sum + i;
            i := i - 1;
        }
      """)


    parser = Parser()
    ast = parser.parse_program(code)

    # Ask user for the unroll depth
    unroll_depth = int(input("Enter the number of times to unroll loops: "))

    # Create a LoopUnroller instance and set the unroll depth
    unroller = LoopUnroller(parser)
    unroller.set_unroll_depth(unroll_depth)  # Set the user-defined unroll depth
    unrolled_ast = unroller.unroll_program(ast)  # Unroll loops in the AST

    print("=== Original Program ===")
    print(code.strip())

    print("\n==== Unrolled Program ====")
    unroller.pretty_print_unrolled_program(unrolled_ast)  # Pretty print the unrolled program

    converter = SSAConverter()
    ssa_program = converter.convert_program(unrolled_ast)  # Convert unrolled AST to SSA

    print("\n==== SSA Form ====")
    pretty_print_ssa(ssa_program)

    print("\n==== SMT-LIB ====")
    print("Generated SMT-LIB:")
    print(generate_smt_lib(ssa_program))

    print("\n==== Verification ====")
    verifier = ProgramVerifier()
    verifier.set_unroll_depth(unroll_depth)
    result = verifier.verify_program(generate_smt_lib(ssa_program))

    if result['status'] == 'success':
        print("✓ " + result['message'])
    elif result['status'] == 'failed':
        print("✗ " + result['message'])
        if 'counterexample' in result:
            print("Counterexample:")
            for var, value in result['counterexample'].items():
                print(f"  {var} = {value}")
    elif result['status'] == 'error':
        print("Error: " + result['message'])
    else:
        print("Verification result: " + result['message'])


    print("\n==== Equivalence Check ====")
    equiChecker = ProgramVerifier()
    equiChecker.set_unroll_depth(unroll_depth)
    equiResult = equiChecker.check_equivalence(program1_code, program2_code)

    if equiResult['equivalent']:
      print("Programs are semantically equivalent!")
    else:
      print("Programs are NOT equivalent!")
      if 'counterexample' in equiResult:
        print("Counterexample:")
        for var, value in equiResult['counterexample'].items():
          print(f"  {var} = {value}")


if __name__ == "__main__":
    main()
