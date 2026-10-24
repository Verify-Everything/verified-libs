#!/usr/bin/env bash
# Run a build step trusting an optional proxy CA passed as the BuildKit secret "ca".
# Without the secret this just runs the command.
if [ -s /run/secrets/ca ]; then
  export SSL_CERT_FILE=/run/secrets/ca CURL_CA_BUNDLE=/run/secrets/ca GIT_SSL_CAINFO=/run/secrets/ca \
         NIX_SSL_CERT_FILE=/run/secrets/ca REQUESTS_CA_BUNDLE=/run/secrets/ca
fi
exec "$@"
