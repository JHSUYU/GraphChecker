package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;

import java.nio.file.Path;
import java.nio.file.Paths;

/** Prints the deterministic digest used to bind generated replay classes. */
public final class ConcolicClassTreeDigest {
    private ConcolicClassTreeDigest() {
    }

    public static void main(String[] argv) throws Exception {
        if (argv.length != 2 || !"--tree".equals(argv[0])) {
            throw new IllegalArgumentException("Usage: --tree <directory>");
        }
        Path tree = Paths.get(argv[1]).toAbsolutePath().normalize();
        ConcolicStaticCatalogReuse.TreeDigest digest =
                ConcolicStaticCatalogReuse.treeDigest(tree);
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "CONCOLIC_CLASS_TREE_DIGEST");
        result.addProperty("authority",
                "SORTED_RELATIVE_PATH_NUL_CONTENT_SHA256_NEWLINE_V1");
        result.addProperty("path", tree.toString());
        result.addProperty("treeSha256", digest.sha256);
        result.addProperty("fileCount", digest.fileCount);
        result.addProperty("complete", true);
        System.out.println(result);
    }
}
