package javaxtools.compiler;

import simulator.CAloops2;

import javax.tools.DiagnosticCollector;
import javax.tools.JavaFileObject;
import java.util.Arrays;
import java.util.Random;

public class UseCompiler {

static final CAloops2 NULL_CA = null;

public static CAloops2 newCA(String source, String qName) {
        CAloops2 myprog;
        CharSequenceCompiler<CAloops2> compiler2;
        try {
            compiler2 = new CharSequenceCompiler<CAloops2>(
                    // Class.forName("compil.Compilo")
                    Class.forName("javaxtools.compiler.UseCompiler").getClassLoader(),
                    Arrays.asList(new String[]{"-target", "1.8"}));
            final DiagnosticCollector<JavaFileObject> errs2 = new DiagnosticCollector<JavaFileObject>();
            Class<CAloops2> compiledCA = compiler2.compile(qName,
                    source, errs2, new Class<?>[]{CAloops2.class});
            // log(errs2);
            //System.out.print("compilation reussie "); 	System.out.print(compiledCA);
            return compiledCA.newInstance();
        } catch (CharSequenceCompilerException e) {
            System.out.print("CharSequenceCompilerException Exeption");
            // log(e.getDiagnostics());
        } catch (ClassNotFoundException e) {
            System.out.print("Ou est compilo??");
        } catch (InstantiationException e) {
            System.out.print("instanciation pb");
            System.out.print(e.getMessage().toString());
        } catch (IllegalAccessException e) {
            System.out.print("illegal access");
            System.out.print(e.getMessage().toString());
        }
        System.out.print("Compilation failed");
        return NULL_CA;
    }
}

