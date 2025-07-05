# MiniScala Compiler

A complete compiler implementation for MiniScala, a functional programming language subset, developed across multiple assignments in CS 352 (Compilers) at Purdue University under Professor Tiark Rompf.

## Project Overview

This repository contains two stages representing different phases of compiler development, built upon skeleton code frameworks provided by the class (as noted in `@author` tags). Stage-1 demonstrates my implementation of core compiler frontend components (Parser and Semantic Analyzer). Stage-2 showcases my work on advanced backend optimization techniques (CPS transformation, Value representations, Optimizations, and Garbage Collection) integrated with a more sophisticated frontend provided in the later assignments by the Professor.

## Repository Structure

```
miniscala-compiler/
├── stage1/                 # Frontend Implementation
│   ├── src/main/scala/project3/
│   │   ├── Parser.scala           # ✅ IMPLEMENTED: Language parsing
│   │   ├── SemanticAnalyzer.scala # ✅ IMPLEMENTED: Type checking
│   │   ├── Interpreter.scala      # ✅ IMPLEMENTED: Stack-based interpreter
│   │   └── Compiler.scala         # ✅ IMPLEMENTED: Basic x86 compiler
│   ├── examples/           # Sample MiniScala programs
│   └── gen/               # Generated assembly output
│
└── stage2/                 # Backend Optimization & Runtime
    ├── compiler/src/miniscala/
    │   ├── CMScalaToCPSTranslator.scala    # ✅ IMPLEMENTED: CPS transformation
    │   ├── CPSValueRepresenter.scala       # ✅ IMPLEMENTED: Value representation
    │   ├── CPSOptimizer.scala              # ✅ IMPLEMENTED: Compiler optimizations
    ├── vm/                # Virtual Machine with GC
    │   ├── src/
    │   │   ├── memory_mark_n_sweep.c      # ✅ IMPLEMENTED: Garbage collector
    │   └── Makefile       # VM build system
    ├── examples/          # Advanced example programs
    └── library/           # Standard library definitions
```

## Stage 1: Frontend Implementation

### Language Features Implemented
- **Type System**: Integer, Boolean, Unit types with full type inference
- **Functions**: First-class functions with parameter passing
- **Arrays**: Dynamic array creation and manipulation
- **Control Flow**: Conditional statements and loops
- **Syntactic Sugar**: Enhanced parsing for common constructs

### Implementation Details

#### Files Implemented by Me:

**Parser.scala** - Complete language parsing implementation
- ✅ **BaseParser**: Parsing infrastructure  
- ✅ **Syntactic Sugar**: Enhanced language constructs
- ✅ **FunctionParser**: Function definition and call parsing
- ✅ **ArrayParser**: Array operation parsing

**SemanticAnalyzer.scala** - Type system implementation
- ✅ **Type Inference**: Complete type checking and inference system
- ✅ **Conformance Checking**: Type compatibility validation

**Interpreter.scala** - Runtime execution
- ✅ **Stack-based Interpreter**: Alternative execution model implementation

**Compiler.scala** - Code generation
- ✅ **x86 Assembly Generation**: Extended basic compiler with new language features

### Running Stage 1
```bash
cd stage1
sbt run examples/valid_arithm.scala           # File execution
sbt run examples/valid_arithm.scala intStack  # Use stack interpreter
```

## Stage 2: Backend Optimization & Runtime

### Advanced Compiler Backend
Stage 2 implements a sophisticated compiler backend with four major components, combining multiple advanced compiler techniques into a single optimized system.

### Implementation Details

#### Files Implemented by Me:

**CMScalaToCPSTranslator.scala** - CPS Transformation
- ✅ **Continuation-Passing Style**: Complete transformation to CPS intermediate representation
- ✅ **Optimized Translations**: Efficient `nonTail`, `tail`, and `cond` implementations
- ✅ **Extended Language Support**: Handling for enhanced syntactic sugar and operators

**CPSValueRepresenter.scala** - Value Representation & Closure Conversion
- ✅ **Efficient Encoding**: Optimized value representation avoiding unnecessary encoding/decoding
- ✅ **Bitwise Optimization**: Left/right shift operations for multiplication/division by 2
- ✅ **Closure Conversion**: Advanced closure conversion supporting recursive and mutually recursive functions
- ✅ **Memory Efficiency**: Smart encoding strategies for primitive operations

**CPSOptimizer.scala** - Compiler Optimizations
- ✅ **Dead Code Elimination**: Removal of unreachable code
- ✅ **Common Subexpression Elimination**: Redundant computation optimization
- ✅ **Constant Folding**: Compile-time constant evaluation
- ✅ **Neutral/Absorbing Elements**: Identity and zero element optimizations
- ✅ **Shrinking Inlining**: Safe, iterative optimizations
- ✅ **General Inlining**: Size-bounded function inlining with Fibonacci growth heuristics

**memory_mark_n_sweep.c** - Garbage Collection
- ✅ **Mark-Sweep Algorithm**: Complete garbage collection implementation
- ✅ **Virtual Address Management**: Proper virtual/physical address handling
- ✅ **Memory Interface**: Implementation of all required memory management interfaces

### Language Enhancements in Stage 2
- **Extended Types**: Char, String, hexadecimal integers
- **Rich Operators**: Bitwise operations, character conversion, I/O operations
- **Advanced Constructs**: Lambda expressions, string literals, boolean short-circuiting
- **Standard Library**: Comprehensive library support with Lists, Pairs, and Arrays

### Running Stage 2
```bash
cd stage2
cd compiler
sbt run ../library/miniscala.lib ../examples/pascal.scala    # Compiles to out.asm

# Build and run with garbage collection
cd ..
cd vm
make                             # Build VM executable
./bin/vm ../compiler/out.asm     # Execute with GC
```

## Architecture Pipeline

### Stage 1 Pipeline
```
Source Code → Parser → Semantic Analyzer → Interpreter/Compiler → Output
```

### Stage 2 Pipeline
```
Source Code → Parser → Semantic Analyzer → CPS Translator → 
Value Representer → Optimizer → Assembly Generator → Virtual Machine
```

## Technical Highlights

### Advanced Compiler Techniques
- **CPS Transformation**: Complete continuation-passing style conversion
- **Closure Conversion**: Efficient closure representation with recursion support
- **Multi-level Optimization**: Shrinking and non-shrinking optimization phases
- **Register Allocation**: Efficient register usage for generated assembly
- **Garbage Collection**: Mark-sweep GC with virtual memory management

### Performance Optimizations
- **Bitwise Arithmetic**: Shift operations for efficient multiplication/division
- **Smart Inlining**: Size-bounded inlining with exponential growth control
- **Efficient Encoding**: Minimal encoding/decoding for primitive operations
- **Memory Management**: Optimized heap allocation with automatic collection

## Testing

Both stages include example files for testing

## Attribution

This project builds upon skeleton code frameworks provided for CS 352 at Purdue University under Professor Tiark Rompf. The skeleton files contain `@author` tags crediting the original framework developers. All files marked with ✅ **IMPLEMENTED** represent my original work, including:

- Frontend implementation (parsing, semantic analysis, interpretation)
- Advanced backend optimizations (CPS transformation, value representation, optimization)
- Memory management system (mark-sweep garbage collection)
