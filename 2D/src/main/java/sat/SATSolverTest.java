package sat;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

import sat.env.Bool;
/*
import static org.junit.Assert.*;

import org.junit.Test;
*/
import sat.env.Environment;
import sat.formula.Clause;
import sat.formula.Formula;
import sat.formula.Literal;
import sat.formula.PosLiteral;

public class SATSolverTest {
    static Literal a = PosLiteral.make("a");
    static Literal b = PosLiteral.make("b");
    Literal c = PosLiteral.make("c");
    static Literal na = a.getNegation();
    Literal nb = b.getNegation();
    Literal nc = c.getNegation();

    /**
    * 
    In main(), read in and parse a .cnf file (see cnf file handout for file format), and construct the corresponding Formula instance as input to your SAT solver. Print out “satisfiable” or “not satisfiable” depending on the result. If the Formula is satisfiable, output your variable assignments to a result file “BoolAssignment.txt” with format of one variable per line: <variable>:<assignment>, e.g.,
    1:TRUE
    2:FALSE
    Report the execution time of your SAT solver by including the following code surrounding your SATSolver.solve():
    Formula f2 = ...
    System.out.println("SAT solver starts!!!"); long started = System.nanoTime(); Environment e = SATSolver.solve(f2);
    long time = System.nanoTime();
    long timeTaken= time - started;
    System.out.println("Time:" + timeTaken/1000000.0 + "ms");
    
    */
    public static void main(String[] args) {
        // testSATSolver1
        Environment e = SATSolver.solve(makeFm(makeCl(a, b)));
        if (Bool.TRUE == e.get(a.getVariable()) || Bool.TRUE == e.get(b.getVariable())) {
            System.out.println("Test 1 passed");
        }
        // testSATSolver2
        e = SATSolver.solve(makeFm(makeCl(na)));
        if (Bool.FALSE == e.get(na.getVariable())) {
            System.out.println("Test 2 passed");
        }

        System.out.println("SAT parser starts!!!");
        long startedParser = System.nanoTime();
        Formula currentFormula = parseFormula("/Volumes/Media/Dls/2D_combined.cnf");
        long timeParser = System.nanoTime();
        long timeTakenParser = timeParser - startedParser;
        System.out.println("Time:" + timeTakenParser / 1000000.0 + "ms");
         System.out.println(currentFormula.toString());

        System.out.println("SAT solver starts!!!");
        long started = System.nanoTime();
        Environment currentE = SATSolver.solve(currentFormula);
        long time = System.nanoTime();
        long timeTaken = time - started;
        System.out.println("Time:" + timeTaken / 1000000.0 + "ms");
        parseOutput(currentE);

    }

    public static Formula parseFormula(String path) {
        String line = null;
        Formula currentFormula = new Formula();

        try {
            BufferedReader bufferedReader = new BufferedReader(new FileReader(path));

            while ((line = bufferedReader.readLine()) != null) {
                if (line.length() > 0) { // check the line is non-empty
                    String firstChar = line.substring(0, 1);

                    if (firstChar.equals("c")) {
                        // System.out.println("It is a comment " + line);
                    } else if (firstChar.equals("p")) {
                        // System.out.println("It is a problem " + line);
                    } else {
                        // System.out.println("It is a clause " + line);
                        String clause[] = line.replaceAll("\\s+", " ").trim().split(" ");
                        Clause currentClause = new Clause();
                        for (String variable : clause) {

                            // System.out.println(variable);

                            if (variable.equals("0")) {
                                break;
                            }
                            Literal currentLiteral;
                            if (variable.startsWith("-")) {
                                currentLiteral = PosLiteral.make(variable.replaceAll("-", ""));
                                currentLiteral = currentLiteral.getNegation();

                            } else {
                                currentLiteral = PosLiteral.make(variable);
                            }

                            // System.out.println(currentLiteral.toString());
                            currentClause = currentClause.add(currentLiteral);
                        }
                        // System.out.println(currentClause.toString());
                        currentFormula = currentFormula.addClause(currentClause);
                    }

                }
            }
            bufferedReader.close();
        } catch (FileNotFoundException ex) {
            System.out.println("Unable to open file '" + path + "'");
        } catch (IOException ex) {
            System.out.println("Error reading file '" + path + "'");
        }
        return currentFormula;
    }

    public static void parseOutput(Environment e) {
        if (e != null) {
            System.out.println("satisfiable");

            String fileName = "BoolAssignment.txt";
            try {
                BufferedWriter bufferedWriter = new BufferedWriter(new FileWriter(fileName));
                bufferedWriter.write(e.toString().replace("Environment:[", "").replace("]", "").replace("->", ":")
                        .replace(", ", "\n"));
                bufferedWriter.close();
            } catch (IOException ex) {
                System.out.println("Error writing to file '" + fileName + "'");
            }

        } else {
            System.out.println("not satisfiable");
        }
    }

    public void testSATSolver1() {
        // (a v b)
        // assertTrue("one of the literals should be set to true",

    }

    public void testSATSolver2() {
        // (~a)
        Environment e = SATSolver.solve(makeFm(makeCl(na)));
        /*
            	assertEquals( Bool.FALSE, e.get(na.getVariable()));
        */
    }

    public void testSATSolver3() {
        Environment e = SATSolver.solve(makeFm(makeCl()));
    }

    private static Formula makeFm(Clause... e) {
        Formula f = new Formula();
        for (Clause c : e) {
            f = f.addClause(c);
        }
        return f;
    }

    private static Clause makeCl(Literal... e) {
        Clause c = new Clause();
        for (Literal l : e) {
            c = c.add(l);
        }
        return c;
    }

}