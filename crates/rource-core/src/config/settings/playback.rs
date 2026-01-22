//! Playback timing settings.

/// Playback settings for animation timing.
#[derive(Debug, Clone)]
pub struct PlaybackSettings {
    /// Seconds of real time per day of commit history.
    pub seconds_per_day: f32,
    /// Auto-skip to next commit after this many seconds of inactivity.
    pub auto_skip_seconds: f32,
    /// Start playback from this timestamp (Unix epoch).
    pub start_timestamp: Option<i64>,
    /// Stop playback at this timestamp (Unix epoch).
    pub stop_timestamp: Option<i64>,
    /// Loop the visualization when reaching the end.
    pub loop_playback: bool,
    /// Start in paused state.
    pub start_paused: bool,
    /// Time scale multiplier (1.0 = normal, 2.0 = double speed).
    pub time_scale: f32,
    /// Stop playback after this many seconds of real time.
    pub stop_at_time: Option<f32>,
    /// Use real-time playback (1 second = 1 second of history).
    pub realtime: bool,
}

impl Default for PlaybackSettings {
    fn default() -> Self {
        Self {
            seconds_per_day: 10.0,
            auto_skip_seconds: 3.0,
            start_timestamp: None,
            stop_timestamp: None,
            loop_playback: false,
            start_paused: false,
            time_scale: 1.0,
            stop_at_time: None,
            realtime: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_playback_settings_default() {
        let playback = PlaybackSettings::default();
        assert!((playback.seconds_per_day - 10.0).abs() < 0.01);
        assert!((playback.auto_skip_seconds - 3.0).abs() < 0.01);
        assert!(!playback.loop_playback);
    }

    #[test]
    fn test_playback_settings_time_controls() {
        let playback = PlaybackSettings::default();
        assert!((playback.time_scale - 1.0).abs() < 0.01);
        assert!(playback.stop_at_time.is_none());
        assert!(!playback.realtime);

        let custom = PlaybackSettings {
            time_scale: 2.0,
            stop_at_time: Some(60.0),
            realtime: true,
            ..Default::default()
        };
        assert!((custom.time_scale - 2.0).abs() < 0.01);
        assert_eq!(custom.stop_at_time, Some(60.0));
        assert!(custom.realtime);
    }
}
