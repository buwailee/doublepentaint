HyperInt, version 1.0
Algorithms for the symbolic integration of hyperlogarithms with applications to Feynman integrals

Copyright (C) 2014 Erik Panzer

#   This program is free software: you can redistribute it and/or modify
#   it under the terms of the GNU General Public License as published by
#   the Free Software Foundation, either version 3 of the License, or
#   (at your option) any later version.
#
#   This program is distributed in the hope that it will be useful,
#   but WITHOUT ANY WARRANTY; without even the implied warranty of
#   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#   GNU General Public License for more details.
#
#   You should have received a copy of the GNU General Public License
#   along with this program.  If not, see <http://www.gnu.org/licenses/>.

To contact the author, please write to

	erik.panzer@all-souls.ox.ac.uk

or visit http://people.maths.ox.ac.uk/panzer/.
Updates, known issues and further information on the program might become available on

	https://bitbucket.org/PanzerErik/hyperint

============================================================================
 1. INSTALLATION AND CONFIGURATION
============================================================================

This program was tested with Maple 16 and should run on any successive version as well. No installation is necessary. During a Maple session, the command

	read "HyperInt.mpl":

loads the program and it is ready to be used. No other files are needed in principle. For a quick start, open the worksheet "Manual.ws" and follow the examples.

However, for most applications it is important that the file periodLookups.m is loaded, so make sure it can be found in Maple's search path. At the beginning of HyperInt.mpl, a variable

	_hyper_autoload_periods := ["periodLookups.m"]:

is defined. You can configure this to any path and put periodLookups.m there. Further period tables can be added to this list for automatic loading during startup. When calculating polynomial reductions, period lookups are not needed so setting _hyper_autoload_periods to an empty list can save memory.

To ensure that HyperInt is working properly, either run

	read "HyperTests.mpl":

in an interactive Maple session, or run the command line version with

	maple HyperTests.mpl

In both cases, the tests must run through without any errors; a final message that all tests passed successfully must be printed. Note that the tests need periodLookups.m. If errors occur during the tests, please inform the author immediately.

The default configurations can be customized at the top of HyperInt.mpl.

============================================================================
 2. FILES IN THIS PACKAGE
============================================================================

HyperInt.mpl
	The complete Maple program in plain text format. Contains general functions to integrate hyperlogarithms, a polynomial reduction routine and tools to compute Feynman integrals. It runs stand-alone, but periodLookups.m is needed for efficient calculations involving periods of higher weight.

Manual.mw
	A standard Maple worksheet that serves its name and shows how to use the functions provided. In particular it contains plenty of examples of Feynman integral calculations.

HyperTests.mpl
	This Maple script (plain text format) contains a series of tests for the program and might further aid getting used to the commands.

periodLookups.m
	A lookup table for multiple zeta values and alternating Euler sums. To reduce the file size it is stored in Maple's internal .m-format. This file should not be modified since wrong period reduction tables will result in wrong outputs of the program.

periodLookups4thRoots.mpl
	This Maple script (plain text format) shows how to supply a custom lookup table, at the example of values of multiple polylogarithms at fourth roots of unity.

IsingE.mpl
	Contains a function to compute Ising class integrals E_n and exact results computed with the program up to n=8. See the manual for details and a reference.

README
	This file.

gpl.txt
	GNU General Public License, version 3.
	
============================================================================
 3. USAGE AND DOCUMENTATION
============================================================================

This implementation and the employed algorithms are explained in the article

	"Algorithms for symbolic integration of hyperlogarithms with applications to Feynman integrals" by E. Panzer
	Computer Physics Communications, 188 (March 2015), pp. 148-166
	doi:10.1016/j.cpc.2014.10.019
	arXiv:1403.3385 [hep-th]

The website hosting the program, updates, and additional material is
	
	https://bitbucket.org/PanzerErik/hyperint

While the above article explains the algorithms in great detail, the usage of the program in practice is best learned by studying the worksheet "Manual.ws". In particular I hope that the examples of Feynman integral computations are illuminating.

If there remain questions or you have any suggestions, please feel free to contact me. Also I would be happy to know when you successfully applied the program and appreciate acknowledgment.

Technical details on hyperlogarithms and the algorithms may also be found in the articles

	- Multiple zeta values and periods of moduli spaces M_0,n(R),
		Annales scientifiques de l'Ecole Normale Superieure 42 (3) (2009) 371--489.
		arXiv:math/0606419.

	- The Massless Higher-Loop Two-Point Function,
		Communications in Mathematical Physics 287 (2009) 925--958.
		arXiv:0804.1660, doi:10.1007/s00220-009-0740-5.

	- On the periods of some Feynman integrals,
		arXiv:0910.0114.

by F.C.S. Brown. Explicit results for Feynman integrals obtained with this program are contained in

	- E. Panzer, On hyperlogarithms and Feynman integrals with divergences and many scales,
		JHEP 03(2014)071. doi:10.1007/JHEP03(2014)071. arXiv:1401.4361.


	- E. Panzer, On the analytic computation of massless propagators in dimensional regularization,
		Nuclear Physics B 874 (2) (2013) 567--593. doi:10.1016/j.nuclphysb.2013.05.025. arXiv:1305.2161.

The method used to regulate divergent parametric integrals introduced in the first of these articles is implemented by HyperInt.

============================================================================
 4. INCLUDED PERIOD TABLES
============================================================================

The file periodLookups.m contains the basis reductions of MZV up to weight 12 and alternating sums up to weight 8 as they are provided by the program zeta_procedures by O. Schnetz. The successor HyperlogProcedures can be downloaded from

	http://www.algeo.math.uni-erlangen.de/?2297

It is based on the data obtained in

J. Bluemlein, D. J. Broadhurst, J. A. M. Vermaseren, The Multiple Zeta Value data mine,
Computer Physics Communications 181 (3) (2010) 582--625. arXiv:0907.2557, doi:10.1016/j.cpc.2009.11.007.

which is available online at

	http://www.nikhef.nl/~form/datamine/datamine.html

============================================================================
 5. KNOWN ISSUES
============================================================================

	- Maple consumes extreme amounts of memory, so keep an eye on it!

	- Only linearly reducible graphs are integrable with HyperInt, by principle.

	- The treatment of rational functions and partial fractions is not optimal (at many intermediate steps, rational functions are factored completely, bringing all parts on a common denominator which may create ridiculously huge polynomials in the numerator). This problem poses a severe bottleneck for practical computations when the integrand has high powers of polynomials in the denominator.
		In principle the workaround is to exploit integration by parts formulae to reduce such integrals with high denominator powers to simpler integrands.

	- Regularization through partial integrations can produce huge integrands when many divergences are present. These are very inefficient to compute with, see the above point.

	- The polynomial reduction seems to contain a considerable number of spurious polynomials for high-dimensional projections. In particular a function might be linearly reducible, but the polynomial reduction contains so many spurious polynomials that this is not detected.
		If one suspects such a situation, one can just integrate as far as linear reducibility is granted by the reduction. Then express this intermediate result in a basis using fibrationBasis(). From the letters that occur one can read off the symbol / the polynomials in the exact Landau variety. If only linear polynomials survive, one can proceed with integration. Otherwise, i.e. when a non-linear polynomial is present for each variable, this is a proof that the function is NOT linearly reducible.

	- For high weights and/or many kinematic invariants, the resulting polylogarithms consist of a huge number of terms. Finding a shortest possible (or symmetry-respecting) representation is not the business of this program; instead there are many articles discussing the symbol and coproduct techniques suitable for this task.
		However, fibrationBasis() at least provides a basis (without any relations), so no hidden zeros remain after applying fibrationBasis().
