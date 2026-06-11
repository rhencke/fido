variable "REGISTRY" {
  default = "ukgartifactory.pe.jfrog.io"
}

variable "IMAGE" {
  default = "fido"
}

variable "TAG" {
  default = "latest"
}

target "fido" {
  context    = "."
  dockerfile = "Dockerfile"
  platforms  = ["linux/amd64", "linux/arm64"]
  tags       = ["${REGISTRY}/${IMAGE}:${TAG}"]
}

group "default" {
  targets = ["fido"]
}
