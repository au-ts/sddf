#!/usr/bin/env python3

import argparse
import logging
import os
import os.path
import re
import shutil
import signal
import subprocess
import sys
import time
from datetime import datetime
from zoneinfo import ZoneInfo
import pexpect

CONFIG_FILE = "pancake.config"
BOARD = "maaxboard2"
DHCP_TIMEOUT = 120  # Increased to account for potential lock waiting with -w flag
SHUTDOWN_TIMEOUT = 10
MAX_RETRIES = 5  # Max retries for mq/iq operations
RETRY_DELAY = 10  # Seconds to wait between retries
SEM_DUMPALL_TIMEOUT = 30  # Timeout for sem dumpall commands (can be slow)

FULL_THROUGHPUTS = [
    10000000,
    20000000,
    50000000,
    100000000,
    200000000,
    300000000,
    400000000,
    500000000,
    600000000,
    700000000,
    800000000,
    900000000,
    1000000000,
]


class Tee:
    def __init__(self, *files):
        self.files = files

    def write(self, data):
        for f in self.files:
            f.write(data)
            f.flush()

    def flush(self):
        for f in self.files:
            f.flush()


class TerminalFormatter(logging.Formatter):
    def format(self, record):
        msg = super().format(record)
        return msg.replace("\n", "\r\n")


def setup_logging(log_file_path):
    logger = logging.getLogger()
    logger.setLevel(logging.INFO)

    file_handler = logging.FileHandler(log_file_path, encoding="utf-8")
    file_handler.setLevel(logging.INFO)
    file_formatter = logging.Formatter("%(asctime)s - %(levelname)s - %(message)s")
    file_handler.setFormatter(file_formatter)

    console_handler = logging.StreamHandler(sys.stdout)
    console_handler.setLevel(logging.INFO)
    console_formatter = TerminalFormatter("%(message)s")
    console_handler.setFormatter(console_formatter)

    logger.addHandler(file_handler)
    logger.addHandler(console_handler)

    return logger


def cleanup_board(use_print=False):
    try:
        msg = "running cleanup routine..."
        if use_print:
            print(msg, flush=True)
        else:
            logging.info(msg)

        result = subprocess.run(
            ["mq", "sem", "-signal", BOARD],
            capture_output=True,
            text=True,
            timeout=5,
        )
        if result.returncode == 0:
            msg = "cleanup complete"
            if use_print:
                print(msg, flush=True)
            else:
                logging.info(msg)
        else:
            msg = f"cleanup returned non-zero exit code: {result.returncode}"
            if use_print:
                print(msg, flush=True)
            else:
                logging.warning(msg)
    except subprocess.TimeoutExpired:
        msg = "cleanup timed out"
        if use_print:
            print(msg, flush=True)
        else:
            logging.warning(msg)
    except Exception as e:
        msg = f"cleanup failed: {e}"
        if use_print:
            print(msg, flush=True)
        else:
            logging.warning(msg)


def check_and_release_stale_locks(use_print=False):
    """Check if any locks are held by us and release them if stale."""
    released_any = False

    # Check mq locks
    try:
        result = subprocess.run(
            ["mq", "sem", "dumpall"],
            capture_output=True,
            text=True,
            timeout=SEM_DUMPALL_TIMEOUT,
        )

        if result.returncode == 0:
            # Parse output to find locks held by samuelt
            # Format: "cheshire1 LOCKED samuelt 2025-10-29 13:45:50.069992383 +1100"
            our_locked_boards = []
            for line in result.stdout.split("\n"):
                if "LOCKED" in line and "samuelt" in line:
                    parts = line.split()
                    if len(parts) >= 2:
                        board_name = parts[0]
                        our_locked_boards.append(board_name)

            if our_locked_boards:
                msg = f"found stale mq locks held by us: {', '.join(our_locked_boards)}"
                if use_print:
                    print(msg, flush=True)
                else:
                    logging.info(msg)

                # Release all our stale locks
                for board_name in our_locked_boards:
                    msg = f"releasing stale lock for {board_name}..."
                    if use_print:
                        print(msg, flush=True)
                    else:
                        logging.info(msg)

                    subprocess.run(
                        ["mq", "sem", "-signal", board_name],
                        capture_output=True,
                        text=True,
                        timeout=5,
                    )
                released_any = True

    except Exception as e:
        msg = f"error checking mq locks: {e}"
        if use_print:
            print(msg, flush=True)
        else:
            logging.warning(msg)

    # Check iq locks
    try:
        result = subprocess.run(
            ["iq", "sem", "dumpall"],
            capture_output=True,
            text=True,
            timeout=SEM_DUMPALL_TIMEOUT,
        )

        if result.returncode == 0:
            our_locked_vbs = []
            for line in result.stdout.split("\n"):
                if "LOCKED" in line and "samuelt" in line:
                    parts = line.split()
                    if len(parts) >= 2:
                        vb_name = parts[0]
                        our_locked_vbs.append(vb_name)

            if our_locked_vbs:
                msg = f"found stale iq locks held by us: {', '.join(our_locked_vbs)}"
                if use_print:
                    print(msg, flush=True)
                else:
                    logging.info(msg)

                for vb_name in our_locked_vbs:
                    msg = f"releasing stale lock for {vb_name}..."
                    if use_print:
                        print(msg, flush=True)
                    else:
                        logging.info(msg)

                    subprocess.run(
                        ["iq", "sem", "-signal", vb_name],
                        capture_output=True,
                        text=True,
                        timeout=5,
                    )
                released_any = True

    except Exception as e:
        msg = f"error checking iq locks: {e}"
        if use_print:
            print(msg, flush=True)
        else:
            logging.warning(msg)

    if released_any:
        msg = "stale locks released"
        if use_print:
            print(msg, flush=True)
        else:
            logging.info(msg)
    else:
        msg = "no stale locks found"
        if use_print:
            print(msg, flush=True)
        else:
            logging.debug(msg)


def check_iq_lock_conflicts():
    """Check if iq locks are held by others. Returns (has_conflicts, our_locks)."""
    try:
        result = subprocess.run(
            ["iq", "sem", "dumpall"],
            capture_output=True,
            text=True,
            timeout=SEM_DUMPALL_TIMEOUT,
        )

        if result.returncode != 0:
            return False, []

        our_locks = []
        other_locks = []

        for line in result.stdout.split("\n"):
            if "LOCKED" in line:
                parts = line.split()
                if len(parts) >= 2:
                    vb_name = parts[0]
                    if "samuelt" in line:
                        our_locks.append(vb_name)
                    else:
                        other_locks.append(vb_name)

        return len(other_locks) > 0, our_locks

    except Exception as e:
        logging.warning(f"error checking iq lock conflicts: {e}")
        return False, []


def run_single_benchmark(folder, throughputs, protocol, mode, benchmark_name):
    log_file_path = f"{folder}/autobench.log"
    setup_logging(log_file_path)

    logging.info("=" * 60)
    logging.info(f"starting benchmark iteration ({mode}, {protocol})")
    logging.info("=" * 60)
    logging.info(f"results will be saved to: {folder}")

    try:
        logging.info("")
        logging.info("=" * 60)
        logging.info("starting mq server...")
        logging.info("(will wait for device lock if held by another process)")
        logging.info("=" * 60)

        pexpect_log = open(f"{folder}/pexpect_output.log", "w", encoding="utf-8")
        tee = Tee(sys.stdout, pexpect_log)

        # Retry loop for mq server start and DHCP
        server = None
        address = None
        for mq_attempt in range(1, MAX_RETRIES + 1):
            try:
                if mq_attempt > 1:
                    logging.info(f"mq attempt {mq_attempt}/{MAX_RETRIES}...")
                    time.sleep(RETRY_DELAY)
                    cleanup_board()  # Clean up any stale state

                server = pexpect.spawn(
                    "mq",
                    [
                        "run",
                        "-w",
                        "8",  # Wait 8 seconds between lock acquisition attempts
                        "-s",
                        BOARD,
                        "-f",
                        "build/loader.img",
                        "-c",
                        "this_is_a_text",
                        "-l",
                        f"{folder}/mq_raw.log",
                    ],
                    timeout=DHCP_TIMEOUT,
                    encoding="utf-8",
                )

                server.logfile_read = tee

                logging.info("")
                logging.info("waiting for dhcp...")
                target = "DHCP request finished, IP address for netif client0 is: "
                try:
                    server.expect_exact(target)
                    address = server.readline().strip()
                    logging.info("")
                    logging.info(f"dhcp complete, ip address: {address}")
                    break  # Success! Exit retry loop
                except pexpect.TIMEOUT:
                    logging.error("")
                    logging.error("dhcp timeout, server did not obtain ip address")
                    if server:
                        server.sendintr()
                        server.wait()
                    if mq_attempt < MAX_RETRIES:
                        logging.warning(
                            f"will retry mq (attempt {mq_attempt}/{MAX_RETRIES})"
                        )
                        continue
                    else:
                        pexpect_log.close()
                        cleanup_board()
                        return 1
                except pexpect.EOF:
                    logging.error("")
                    logging.error("mq exited unexpectedly before dhcp")
                    if mq_attempt < MAX_RETRIES:
                        logging.warning(
                            f"will retry mq (attempt {mq_attempt}/{MAX_RETRIES})"
                        )
                        continue
                    else:
                        pexpect_log.close()
                        cleanup_board()
                        return 1

            except Exception as e:
                logging.error(f"mq server start failed: {e}")
                if server:
                    try:
                        server.sendintr()
                        server.wait()
                    except:
                        pass
                if mq_attempt < MAX_RETRIES:
                    logging.warning(
                        f"will retry mq (attempt {mq_attempt}/{MAX_RETRIES})"
                    )
                    continue
                else:
                    pexpect_log.close()
                    cleanup_board()
                    return 1

        if not address:
            logging.error("failed to obtain ip address after all retries")
            pexpect_log.close()
            cleanup_board()
            return 1

        logging.info("")
        logging.info("=" * 60)
        logging.info("starting iq benchmark client...")
        logging.info("(will wait for device locks if held by another process)")
        logging.info("=" * 60)
        logging.info(f"protocol: {protocol}")
        logging.info(
            f"testing throughputs: {', '.join(f'{t / 1e9:.1f}Gbps' for t in throughputs)}"
        )

        # Retry loop for iq client
        iq_success = False
        for iq_attempt in range(1, MAX_RETRIES + 1):
            try:
                if iq_attempt > 1:
                    logging.info(f"iq attempt {iq_attempt}/{MAX_RETRIES}...")
                    time.sleep(RETRY_DELAY)

                # Check and release any stale iq locks before starting
                logging.info("checking for stale iq locks before starting...")
                has_conflicts, our_locks = check_iq_lock_conflicts()
                if our_locks:
                    logging.warning(
                        f"releasing our stale iq locks: {', '.join(our_locks)}"
                    )
                    for vb_name in our_locks:
                        subprocess.run(
                            ["iq", "sem", "-signal", vb_name],
                            capture_output=True,
                            text=True,
                            timeout=5,
                        )
                if has_conflicts:
                    logging.warning(
                        "some iq locks are held by other users - will wait for them"
                    )

                iq_args = [
                    "run",
                    "-w",
                    "8",  # Wait 8 seconds between lock acquisition attempts
                    "-f",
                    "benchmark.py",
                    "-b",
                    "-c",
                    "vb01",
                    "-c",
                    "vb02",
                    "-c",
                    "vb03",
                    "-c",
                    "vb04",
                    "-l",
                    f"{folder}/iq.log",
                    "--",
                    address,
                    "--clients",
                    "vb01",
                    "vb02",
                    "vb03",
                    "vb04",
                ]

                if protocol == "TCP":
                    iq_args.append("--tcp")

                iq_args.extend(["--throughputs", *map(str, throughputs)])

                client = pexpect.spawn(
                    "iq",
                    iq_args,
                    timeout=None,
                    encoding="utf-8",
                )

                client.logfile_read = tee

                logging.info("monitoring iq client output...")
                iq_lock_error = False
                iq_failed = False
                has_result_summary = False
                try:
                    while True:
                        try:
                            index = client.expect(
                                [pexpect.EOF, "(?i)lock.*held by", "Result Summary:"],
                                timeout=0.1,
                            )
                            if index == 0:
                                break
                            elif index == 1:
                                logging.warning("lock conflict detected in iq")
                                iq_lock_error = True
                                client.sendintr()
                                client.expect(pexpect.EOF, timeout=10)
                                break
                            elif index == 2:
                                logging.info("detected result summary in iq output")
                                has_result_summary = True
                                # Don't break, let it finish naturally
                        except pexpect.TIMEOUT:
                            continue
                except pexpect.EOF:
                    pass

                exit_code = client.wait()

                # If iq had lock errors, check what went wrong
                if iq_lock_error:
                    logging.info("checking iq lock status...")
                    has_conflicts, our_locks = check_iq_lock_conflicts()

                    if our_locks:
                        logging.warning(
                            f"iq locks still held by us: {', '.join(our_locks)}"
                        )
                        logging.info("releasing our stale iq locks...")
                        for vb_name in our_locks:
                            subprocess.run(
                                ["iq", "sem", "-signal", vb_name],
                                capture_output=True,
                                text=True,
                                timeout=5,
                            )
                        logging.info("stale iq locks released")

                    if has_conflicts:
                        logging.error("iq locks are held by another user")
                        logging.error(
                            "benchmark cannot continue - another user is using iq devices"
                        )
                        server.sendintr()
                        server.wait()
                        pexpect_log.close()
                        cleanup_board()
                        return 1

                    # If we had our own locks and no conflicts, might have been transient - retry
                    if iq_attempt < MAX_RETRIES:
                        logging.warning(
                            f"iq lock issues detected, will retry (attempt {iq_attempt}/{MAX_RETRIES})"
                        )
                        continue
                    else:
                        logging.error("iq failed after all retries")
                        server.sendintr()
                        server.wait()
                        pexpect_log.close()
                        cleanup_board()
                        return 1

                # Check if iq actually succeeded by looking for result summary
                # iq sometimes returns non-zero exit code even on success
                if has_result_summary:
                    logging.info(
                        "iq client completed successfully (result summary found)"
                    )
                    if exit_code != 0:
                        logging.info(
                            f"note: iq exited with code {exit_code} but results were generated"
                        )
                    iq_success = True
                    break

                # If no result summary, check if iq failed
                if exit_code != 0 or iq_failed:
                    logging.warning(
                        f"iq exited with code {exit_code} and no results found"
                    )
                    if iq_attempt < MAX_RETRIES:
                        logging.warning(
                            f"will retry iq (attempt {iq_attempt}/{MAX_RETRIES})"
                        )
                        continue
                    else:
                        logging.error("iq failed after all retries")
                        server.sendintr()
                        server.wait()
                        pexpect_log.close()
                        cleanup_board()
                        return 1

                # Success!
                logging.info("iq client finished successfully")
                iq_success = True
                break

            except Exception as e:
                logging.error(f"iq client failed with exception: {e}")
                if iq_attempt < MAX_RETRIES:
                    logging.warning(
                        f"will retry iq (attempt {iq_attempt}/{MAX_RETRIES})"
                    )
                    continue
                else:
                    logging.error("iq failed after all retries")
                    server.sendintr()
                    server.wait()
                    pexpect_log.close()
                    cleanup_board()
                    return 1

        if not iq_success:
            logging.error("iq client did not complete successfully after all retries")
            server.sendintr()
            server.wait()
            pexpect_log.close()
            cleanup_board()
            return 1

        logging.info("waiting 10s after iq finishes...")
        time.sleep(10)

        logging.info("")
        logging.info("=" * 60)
        logging.info("shutting down mq server...")
        logging.info("=" * 60)
        server.sendintr()
        try:
            server.expect(pexpect.EOF, timeout=SHUTDOWN_TIMEOUT)
            logging.info("server shut down gracefully")
        except pexpect.TIMEOUT:
            logging.warning("server did not terminate gracefully, force killing...")
            server.terminate(force=True)

        server.wait()

        pexpect_log.close()

        logging.info("")
        logging.info("=" * 60)
        logging.info("processing logs...")
        logging.info("=" * 60)

        iq_log_path = f"{folder}/iq.log"
        if os.path.exists(iq_log_path):
            logging.info("extracting csv results from iq.log...")
            try:
                with open(iq_log_path, "r") as f:
                    content = f.read()

                if "Result Summary:" in content:
                    parts = content.split("Result Summary:")
                    if len(parts) > 1:
                        csv_section = parts[1].strip()
                        csv_lines = []
                        for line in csv_section.split("\n"):
                            line = line.strip()
                            if line:
                                csv_lines.append(line)
                            else:
                                break

                        if len(csv_lines) >= 2:
                            csv_path = f"{folder}/results.csv"
                            with open(csv_path, "w") as csv_file:
                                csv_file.write("\n".join(csv_lines) + "\n")
                            logging.info(f"csv results saved to: {csv_path}")
                        else:
                            logging.warning(
                                "result summary found but no csv data extracted"
                            )
                    else:
                        logging.warning(
                            "result summary marker found but no data after it"
                        )
                else:
                    logging.warning("no result summary found in iq.log")
            except Exception as e:
                logging.error(f"failed to extract csv from iq.log: {e}")
        else:
            logging.warning(f"iq.log not found at {iq_log_path}")

        if os.path.exists(f"{folder}/mq_raw.log"):
            logging.info("stripping ansi escape codes from mq log...")
            with (
                open(f"{folder}/mq_raw.log", "r") as f1,
                open(f"{folder}/mq.log", "w") as f2,
            ):
                pattern = re.compile(
                    r"\x1b(\[[0-?]*[ -/]*[@-~]|\][ -~]*(\x07|\x1b\\))|(\x00)|(\x05)|(\x08)"
                )
                f2.writelines(pattern.sub("", line) for line in f1.readlines())
            os.remove(f"{folder}/mq_raw.log")
            logging.info(f"clean mq log saved to: {folder}/mq.log")

            logging.info("processing mq.log to extract json metrics...")
            process_script = "process_output.py"
            mq_json_path = f"{folder}/mq_metrics.json"
            try:
                result = subprocess.run(
                    ["python3", process_script, "-j", f"{folder}/mq.log"],
                    capture_output=True,
                    text=True,
                    check=True,
                )
                with open(mq_json_path, "w") as json_file:
                    json_file.write(result.stdout)
                logging.info(f"mq metrics json saved to: {mq_json_path}")
            except subprocess.CalledProcessError as e:
                logging.error(f"failed to process mq.log: {e}")
                logging.error(f"stderr: {e.stderr}")
            except Exception as e:
                logging.error(f"error running process_microkit_output.py: {e}")
        else:
            logging.warning("mq_raw.log not found, skipping log processing")
            cleanup_board()
            return 1

        logging.info("")
        logging.info("=" * 60)
        logging.info("benchmark complete")
        logging.info("=" * 60)
        if benchmark_name:
            logging.info(f"benchmark name: {benchmark_name}")
        logging.info(f"mode: {mode}")
        logging.info(f"protocol: {protocol}")
        logging.info(f"results directory: {folder}")
        logging.info(f"ip address obtained: {address}")
        logging.info(f"throughputs tested: {len(throughputs)}")
        logging.info(f"logs and results saved:")
        logging.info(f"  - benchmark script log: {log_file_path}")
        logging.info(f"  - mq/iq output: {folder}/pexpect_output.log")
        logging.info(f"  - mq clean log: {folder}/mq.log")
        logging.info(f"  - iq full log: {folder}/iq.log")

        csv_path = f"{folder}/results.csv"
        if os.path.exists(csv_path):
            logging.info(f"  - iq csv results: {csv_path}")

        mq_json_path = f"{folder}/mq_metrics.json"
        if os.path.exists(mq_json_path):
            logging.info(f"  - mq metrics json: {mq_json_path}")

        logging.info("")
        cleanup_board()

        return 0

    except KeyboardInterrupt:
        logging.error("")
        logging.error("benchmark interrupted by user")
        cleanup_board()
        return 1
    except Exception as e:
        logging.error("")
        logging.error(f"benchmark failed with error: {e}")
        cleanup_board()
        return 1


def main():
    parser = argparse.ArgumentParser(
        description="Automated benchmarking for SDDF echo server"
    )
    parser.add_argument(
        "--dryrun",
        action="store_true",
        help="Run quick test with only 1Gbps throughput (default: run full benchmark)",
    )
    parser.add_argument(
        "--tcp",
        action="store_true",
        help="Use TCP protocol (default: UDP)",
    )
    parser.add_argument(
        "--name",
        type=str,
        default="",
        help="Name for this benchmark run (will be prepended to timestamp in folder name)",
    )
    parser.add_argument(
        "--iter",
        type=int,
        default=1,
        help="Number of times to repeat the benchmark (default: 1)",
    )
    args = parser.parse_args()

    if args.dryrun:
        throughputs = [1000000000]
        mode = "DRY RUN - 1Gbps only"
    else:
        throughputs = FULL_THROUGHPUTS
        mode = "FULL RUN"

    protocol = "TCP" if args.tcp else "UDP"

    print("=" * 60, flush=True)
    print(f"starting automated benchmark ({mode}, {protocol})", flush=True)
    if args.iter > 1:
        print(f"total iterations: {args.iter}", flush=True)
    print("=" * 60, flush=True)

    print("checking for stale locks from previous runs...", flush=True)
    check_and_release_stale_locks(use_print=True)
    print("", flush=True)

    print("cleaning build directory...", flush=True)
    try:
        shutil.rmtree("build")
    except FileNotFoundError:
        pass

    print(f"building with {CONFIG_FILE}...", flush=True)
    try:
        subprocess.run(
            ["make", f"CONFIG_FILE={CONFIG_FILE}", "-j8"],
            check=True,
        )
    except subprocess.CalledProcessError as e:
        print(f"build failed with exit code {e.returncode}", flush=True)
        return 1

    print("build complete", flush=True)
    print("", flush=True)

    if args.iter > 1:
        main_timestamp = datetime.now(ZoneInfo("Australia/Sydney")).strftime(
            "%d%m%y-%H%M%S"
        )
        if args.name:
            main_folder_name = f"{args.name}-batch-{main_timestamp}"
        else:
            main_folder_name = f"batch-{main_timestamp}"
        main_folder = os.path.abspath(f"results/{main_folder_name}")
        os.makedirs(main_folder)
        print(f"running {args.iter} iterations, results in: {main_folder}", flush=True)
    else:
        main_folder = os.path.abspath("results")

    for i in range(1, args.iter + 1):
        if args.iter > 1:
            print("")
            print("=" * 60, flush=True)
            print(f"starting iteration {i}/{args.iter}", flush=True)
            print("=" * 60, flush=True)
            time.sleep(1)

        iter_timestamp = datetime.now(ZoneInfo("Australia/Sydney")).strftime(
            "%d%m%y-%H%M%S"
        )
        if args.iter > 1:
            if args.name:
                iter_folder_name = f"{args.name}-iter{i}-{iter_timestamp}"
            else:
                iter_folder_name = f"iter{i}-{iter_timestamp}"
            folder = os.path.join(main_folder, iter_folder_name)
        else:
            if args.name:
                iter_folder_name = f"{args.name}-{iter_timestamp}"
            else:
                iter_folder_name = iter_timestamp
            folder = os.path.join(main_folder, iter_folder_name)

        os.makedirs(folder)

        result = run_single_benchmark(folder, throughputs, protocol, mode, args.name)

        if result != 0:
            print(f"iteration {i} failed, stopping", flush=True)
            return result

        logging.getLogger().handlers.clear()

        if i < args.iter:
            print(f"waiting between iterations...", flush=True)
            # Give the system time to fully release the lock
            time.sleep(5)
            # Check for and release any stale locks
            print(f"checking for stale locks...", flush=True)
            check_and_release_stale_locks(use_print=True)
            # Wait a bit more before next iteration
            time.sleep(5)

    if args.iter > 1:
        print("")
        print("=" * 60, flush=True)
        print("all iterations complete", flush=True)
        print("=" * 60, flush=True)
        print(f"total iterations: {args.iter}", flush=True)
        print(f"results directory: {main_folder}", flush=True)

    return 0


if __name__ == "__main__":
    sys.exit(main())
