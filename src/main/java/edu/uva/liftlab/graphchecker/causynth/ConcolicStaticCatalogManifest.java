package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

/** Creates the immutable manifest consumed by concolic static-catalog reuse. */
public final class ConcolicStaticCatalogManifest {
    private ConcolicStaticCatalogManifest() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        JsonObject manifest = ConcolicStaticCatalogReuse.createManifest(
                arguments.regions, arguments.coverage, arguments.staticGraph,
                arguments.regionEdges, arguments.targetSpec,
                arguments.originalClasses, arguments.supplementalTrees,
                arguments.staticProcessProvenance, arguments.sourceRevision);
        ConcolicStaticCatalogReuse.writeManifest(arguments.output, manifest);
        System.out.println(arguments.output.toAbsolutePath().normalize());
    }

    static final class Arguments {
        private Path output;
        private Path regions;
        private Path coverage;
        private Path staticGraph;
        private Path regionEdges;
        private Path targetSpec;
        private Path originalClasses;
        private Path staticProcessProvenance;
        private String sourceRevision = "";
        private final List<Path> supplementalTrees = new ArrayList<>();

        private static Arguments parse(String[] argv) {
            Arguments result = new Arguments();
            for (int index = 0; index < argv.length; index++) {
                String option = argv[index];
                if (index + 1 >= argv.length) {
                    throw new IllegalArgumentException("Missing value for " + option);
                }
                String value = argv[++index];
                switch (option) {
                    case "--output":
                        result.output = Paths.get(value);
                        break;
                    case "--regions":
                        result.regions = Paths.get(value);
                        break;
                    case "--coverage":
                        result.coverage = Paths.get(value);
                        break;
                    case "--static-graph":
                        result.staticGraph = Paths.get(value);
                        break;
                    case "--region-edges":
                        result.regionEdges = Paths.get(value);
                        break;
                    case "--target-spec":
                        result.targetSpec = Paths.get(value);
                        break;
                    case "--original-classes":
                        result.originalClasses = Paths.get(value);
                        break;
                    case "--supplemental-tree":
                        result.supplementalTrees.add(Paths.get(value));
                        break;
                    case "--static-process-provenance":
                        result.staticProcessProvenance = Paths.get(value);
                        break;
                    case "--source-revision":
                        result.sourceRevision = value;
                        break;
                    default:
                        throw new IllegalArgumentException("Unknown option " + option);
                }
            }
            if (result.output == null || result.regions == null
                    || result.coverage == null || result.staticGraph == null
                    || result.regionEdges == null || result.targetSpec == null
                    || result.originalClasses == null
                    || result.staticProcessProvenance == null) {
                throw new IllegalArgumentException("Incomplete static catalog "
                        + "manifest arguments");
            }
            return result;
        }
    }
}
