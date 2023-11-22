# CTL Model Checker using Python

Overview
This Python code provides a comprehensive framework for performing Computation Tree Logic (CTL) model checking on a given transition system. CTL is a branching-time temporal logic used to reason about the possible future states of a system. The code defines classes and functions for working with logical expressions in CTL, including both binary and unary operators. The main objective is to determine whether a given CTL formula is valid in a finite CTL model.

Credits
This code is built upon the NFA (Non-deterministic Finite Automaton) framework created by Professor Vincent Hugot, a member of the SDS team at LIFO INSA CVL in Bourges, France. The NFA framework can be cloned from https://github.com/vincent-hugot.

Usage
To use this code, follow these steps:

Clone the NFA framework from https://github.com/vincent-hugot.
Copy the provided CTL model checking Python code into your project.
Import the necessary modules and classes from the NFA framework.
Define your CTL formula and transition system.
Utilize the Sat function to evaluate the CTL formula and determine which states satisfy the formula.
Code Structure
The code defines classes for various binary and unary operators used in CTL expressions.
The Sat function is the main function for model checking. It evaluates a CTL formula in a given transition system and returns the set of states satisfying the formula.
The code includes functions for simplifying CTL formulas and handling different CTL operators such as EU (Exist Until), AU (All Until), EX (Exist Next), and more.
Visualization functions (checkvisu) are provided for visualizing the atoms and simplified versions of CTL formulas.
Examples
The code includes several test cases showcasing the usage of different CTL formulas. Uncomment and modify the examples in the code to experiment with your own CTL formulas and transition systems.

Dependencies
Python 3.x
NFA framework from https://github.com/vincent-hugot
Feel free to explore and adapt the code for your specific CTL model checking needs. If you encounter any issues or have suggestions for improvements, please don't hesitate to reach out. Happy model checking!





