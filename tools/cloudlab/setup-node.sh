#!/usr/bin/env bash
set -euo pipefail
server=${1:?usage: setup-node.sh <bulk server host> <subnet> <disk>}
subnet=${2:?usage: setup-node.sh <bulk server host> <subnet> <disk>}
disk=${3:?usage: setup-node.sh <bulk server host> <subnet> <disk>}
me=$(hostname -s)
user=$(id -un)
export DEBIAN_FRONTEND=noninteractive
sudo apt-get update -qq
sudo apt-get install -y -qq openjdk-8-jdk maven ant nfs-common docker.io unzip zip rsync python3 jq git >/dev/null
[[ "${me}" != "${server}" ]] || sudo apt-get install -y -qq nfs-kernel-server >/dev/null
sudo update-alternatives --set java /usr/lib/jvm/java-8-openjdk-amd64/jre/bin/java >/dev/null
sudo update-alternatives --set javac /usr/lib/jvm/java-8-openjdk-amd64/bin/javac >/dev/null
sudo ln -sfn /usr/share/maven /usr/lib/maven
# Replays run the Zero interpreter one thread each, so a core's clock is their speed: hold every core at the
# performance governor (CloudLab's default schedutil kept busy cores at 2.4-2.8 of 3.7 GHz).
for governor in /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor; do
  [[ ! -w "${governor}" && ! -e "${governor}" ]] || echo performance | sudo tee "${governor}" >/dev/null
done
if ! mountpoint -q /data; then
  sudo blkid "${disk}" >/dev/null 2>&1 || sudo mkfs.ext4 -q -F -m 0 "${disk}"
  sudo mkdir -p /data
  grep -q "^${disk} " /etc/fstab || echo "${disk} /data ext4 defaults,noatime 0 2" | sudo tee -a /etc/fstab >/dev/null
  sudo mount /data
fi
sudo mkdir -p /data/localtmp /localtmp /bulk
sudo chmod 1777 /data/localtmp
grep -q ' /localtmp ' /etc/fstab || echo '/data/localtmp /localtmp none bind 0 0' | sudo tee -a /etc/fstab >/dev/null
mountpoint -q /localtmp || sudo mount /localtmp
mkdir -p "/localtmp/${user}"
if [[ "${me}" == "${server}" ]]; then
  sudo mkdir -p /data/bulk
  sudo chown "${user}:$(id -gn)" /data/bulk
  grep -q '^/data/bulk ' /etc/exports || echo "/data/bulk ${subnet}(rw,async,no_subtree_check,no_root_squash)" | sudo tee -a /etc/exports >/dev/null
  sudo exportfs -ra
  sudo systemctl enable --now nfs-kernel-server >/dev/null 2>&1
  grep -q ' /bulk ' /etc/fstab || echo '/data/bulk /bulk none bind 0 0' | sudo tee -a /etc/fstab >/dev/null
else
  grep -q ' /bulk ' /etc/fstab || echo "${server}:/data/bulk /bulk nfs rw,hard,noatime,vers=4.2,rsize=1048576,wsize=1048576,actimeo=1 0 0" | sudo tee -a /etc/fstab >/dev/null
fi
mountpoint -q /bulk || sudo mount /bulk
mkdir -p /bulk/bin /bulk/m2/dot-m2 "${HOME}/.local/bin"
mkdir -p /bulk/m2/dot-ivy2 /bulk/m2/dot-ant
for dot in m2 ivy2 ant; do
  [[ -L "${HOME}/.${dot}" ]] || { [[ ! -e "${HOME}/.${dot}" ]] || mv "${HOME}/.${dot}" "${HOME}/.${dot}.local"; ln -sfn "/bulk/m2/dot-${dot}" "${HOME}/.${dot}"; }
done
sudo usermod -aG docker "${user}"
echo "${me}: ready"
