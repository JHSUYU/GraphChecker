#!/usr/bin/env bash
set -euo pipefail

output=${SOLR_ANALYSIS_CLASSES:-/tmp/solr18406-analysis-classes}
mkdir -p "${output}"
find "${output}" -type f -delete

copy_family() {
  local root=$1 family=$2 file
  while IFS= read -r file; do
    mkdir -p "${output}/$(dirname "${file}")"
    cp "${root}/${file}" "${output}/${file}"
  done < <(cd "${root}" && find "$(dirname "${family}")" \
    -maxdepth 1 -type f -name "$(basename "${family}")*.class" | sort)
}

core=/opt/solr/solr/build/solr-core/classes/java
solrj=/opt/solr/solr/build/solr-solrj/classes/java
copy_family "${core}" org/apache/solr/core/IndexDeletionPolicyWrapper
copy_family "${core}" org/apache/solr/handler/IndexFetcher
copy_family "${core}" org/apache/solr/handler/ReplicationHandler
copy_family "${core}" org/apache/solr/servlet/HttpSolrCall
copy_family "${solrj}" edu/uva/liftlab/graphchecker/annotation/CausynthExceptionTarget
copy_family "${solrj}" org/apache/solr/client/solrj/impl/HttpSolrClient
